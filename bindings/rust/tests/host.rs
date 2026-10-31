use leanelpi::{Program, Term};

const GRAPH: &str = "kind node type.\n\
                     type a, b, c, d, x, y node.\n\
                     pred edge i:node, o:node.\n\
                     pred path i:node, o:node.\n\
                     path X Y :- edge X Y.\n\
                     path X Z :- edge X Y, path Y Z.";

const EDGES: [(&str, &str); 4] = [("a", "b"), ("b", "c"), ("c", "d"), ("x", "y")];

fn graph() -> Program {
    Program::new(GRAPH).unwrap().declare("edge", "pred edge i:node, o:node.").unwrap()
}

fn c(n: &str) -> Term {
    Term::Const(n.into())
}

// @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host predicate answers a recursive query]]
#[test]
fn host_edges_answer_a_recursive_query() {
    let p = graph();
    let mut calls = Vec::new();
    let run = p
        .solve_host("path a X", 0, 0, |name, args| {
            assert_eq!(name, "edge");
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1], Term::Var(_)), "the output argument is unbound: {:?}", args[1]);
            let Term::Const(from) = &args[0] else { return Err(format!("unbound source {:?}", args[0])) };
            calls.push(from.clone());
            Ok(EDGES.iter().filter(|e| e.0 == from).map(|e| vec![c(e.1)]).collect())
        })
        .unwrap();
    let xs: Vec<_> = run.solutions.iter().map(|s| s.terms["X"].clone()).collect();
    assert_eq!(xs, [c("b"), c("c"), c("d")]);
    assert_eq!(run.solutions[0].bindings["X"], "b");
    assert!(run.exhausted);
    assert!(run.fuel_used > 0);
    // each clause of path calls edge once: eager, one callback per call
    assert_eq!(calls, ["a", "a", "b", "b", "c", "c", "d", "d"]);

    // the limit stops the search, and the program keeps working afterwards
    let run = p.solve_host("path a X", 1, 0, |_, args| {
        let Term::Const(from) = &args[0] else { unreachable!() };
        Ok(EDGES.iter().filter(|e| e.0 == from).map(|e| vec![c(e.1)]).collect())
    });
    let run = run.unwrap();
    assert_eq!(run.solutions.len(), 1);
    assert!(!run.exhausted);

    // no rows is failure, not an error
    let run = p.solve_host("path a X", 0, 0, |_, _| Ok(vec![])).unwrap();
    assert!(run.solutions.is_empty());
}

// @tg: verifies:: [[openspec:language-bindings#Structured answers#Terms decode by kind]]
#[test]
fn structured_terms() {
    let p = Program::new(
        "kind pt type.\ntype pt int -> string -> pt.\n\
         pred v o:int, o:string, o:pt, o:list int, o:float.\n\
         v 42 \"hi\" (pt 1 \"x\") [1, 2] 1.5.",
    )
    .unwrap();
    let s = p.first("v I S P L F").unwrap().unwrap();
    assert_eq!(s.terms["I"], Term::Int(42));
    assert_eq!(s.terms["S"], Term::Str("hi".into()));
    assert_eq!(s.terms["P"], Term::App("pt".into(), vec![Term::Int(1), Term::Str("x".into())]));
    assert_eq!(s.terms["L"].as_list().unwrap(), [&Term::Int(1), &Term::Int(2)]);
    assert_eq!(s.terms["L"], Term::list(vec![Term::Int(1), Term::Int(2)]));
    assert_eq!(s.terms["F"], Term::Float(1.5));
    assert_eq!(s.bindings["P"], "pt 1 \"x\"");

    // a λ-term is printed; an unassigned variable is a variable
    let s = Program::new("pred id o:(int -> int).\nid (x\\ x).").unwrap().first("id F, G = G").unwrap().unwrap();
    assert!(matches!(&s.terms["F"], Term::Other(o) if o.contains('\\')), "{:?}", s.terms["F"]);
    assert!(matches!(&s.terms["G"], Term::Var(_)), "{:?}", s.terms["G"]);

    // terms a host returns reach the program intact
    let h = p.declare("mk", "pred mk o:pt, o:float, o:list int.").unwrap();
    let run = h
        .solve_host("mk P F L", 0, 0, |_, args| {
            assert_eq!(args.len(), 3);
            Ok(vec![vec![
                Term::App("pt".into(), vec![Term::Int(7), Term::Str("q".into())]),
                Term::Float(2.25),
                Term::list(vec![Term::Int(3)]),
            ]])
        })
        .unwrap();
    let s = &run.solutions[0];
    assert_eq!(s.bindings["P"], "pt 7 \"q\"");
    assert_eq!(s.terms["F"], Term::Float(2.25));
    assert_eq!(s.terms["L"], Term::list(vec![Term::Int(3)]));

    // JSON round trip of the tree form; an integer outside i64 decodes as Other
    let t = Term::App("f".into(), vec![Term::Int(-3), Term::Var("X".into()), Term::Other("c0 \\ c0".into())]);
    let j = serde_json::to_string(&t).unwrap();
    assert_eq!(j, r#"{"a":[{"i":-3},{"v":"X"},{"o":"c0 \\ c0"}],"c":"f"}"#);
    assert_eq!(serde_json::from_str::<Term>(&j).unwrap(), t);
    assert_eq!(serde_json::from_str::<Term>(r#"{"i":18446744073709551615}"#).unwrap(), Term::Other("18446744073709551615".into()));
}

// @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host errors are reported]]
#[test]
fn host_errors_propagate() {
    let p = graph();
    let e = p.solve_host("path a X", 0, 0, |_, _| Err("table is offline".into())).unwrap_err();
    assert!(e.message().contains("table is offline"), "{e}");
    assert!(e.message().contains("edge"), "{e}");
    assert!(!e.is_out_of_fuel());

    // a constant the program does not know is an error, not a silent failure
    let e = p.solve_host("path a X", 0, 0, |_, _| Ok(vec![vec![c("nowhere")]])).unwrap_err();
    assert!(e.message().contains("nowhere"), "{e}");

    // a row with the wrong number of terms
    let e = p.solve_host("path a X", 0, 0, |_, _| Ok(vec![vec![c("b"), c("c")]])).unwrap_err();
    assert!(e.message().contains("expected 1"), "{e}");

    // an unknown name or a clash is a declaration error
    assert!(Program::new(GRAPH).unwrap().declare("edge", "pred other o:int.").is_err());
    assert!(Program::new(GRAPH).unwrap().declare("path", "pred path i:node, o:node.").is_err());
}

// @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Out of fuel is distinguishable]]
#[test]
fn out_of_fuel_is_detected() {
    let p = Program::new("pred loop i:int.\nloop N :- loop N.").unwrap();
    let e = p.solve_with("loop 1", None, Some(1000)).unwrap_err();
    assert!(e.is_out_of_fuel(), "{e}");
    let h = p.declare("tick", "pred tick o:int.").unwrap();
    let e = h.solve_host("loop 1", 0, 1000, |_, _| Ok(vec![])).unwrap_err();
    assert!(e.is_out_of_fuel(), "{e}");
    // a finished run reports the fuel it took
    let run = h.solve_host("tick X", 0, 1000, |_, _| Ok(vec![vec![Term::Int(1)]])).unwrap();
    assert!(run.fuel_used > 0 && run.fuel_used <= 1000, "{}", run.fuel_used);
}

// @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host predicate without a host]]
#[test]
fn declared_predicate_via_plain_solve_errors() {
    let p = graph();
    let e = p.solve("path a X").unwrap_err();
    assert!(e.message().contains("host"), "{e}");
    // the undeclared original is unaffected
    assert!(Program::new(GRAPH).unwrap().solve("path a X").unwrap().is_empty());
}

// @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Panics do not cross the boundary]]
#[test]
fn panic_in_callback_becomes_an_error() {
    let p = graph();
    let e = p.solve_host("path a X", 0, 0, |_, _| panic!("kaboom")).unwrap_err();
    assert!(e.message().contains("panicked") && e.message().contains("kaboom"), "{e}");
    // the runtime is still usable
    let run = p.solve_host("path x X", 0, 0, |_, args| Ok(if args[0] == c("x") { vec![vec![c("y")]] } else { vec![] })).unwrap();
    assert_eq!(run.solutions.len(), 1);
}
