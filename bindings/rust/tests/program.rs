use leanelpi::Program;

const APP: &str = "pred app i:list int, i:list int, o:list int.\n\
                   app [] L L.\napp [X|Xs] L [X|R] :- app Xs L R.";

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Load and query]]
#[test]
fn version_is_semver() {
    assert_eq!(leanelpi::version().unwrap().matches('.').count(), 2);
}

// @tg: verifies:: [[openspec:language-bindings#Rust binding#Query from Rust]]
#[test]
fn first_solution() {
    let p = Program::new(APP).unwrap();
    let s = p.first("app [1,2] [3] R").unwrap().unwrap();
    assert_eq!(s.bindings["R"], "[1, 2, 3]");
}

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Limit stops the search]]
#[test]
fn all_solutions_and_limit() {
    let p = Program::new("pred n o:int.\nn 1.\nn 2.\nn 3.").unwrap();
    let all: Vec<_> = p.solve("n X").unwrap().into_iter().map(|s| s.bindings["X"].clone()).collect();
    assert_eq!(all, ["1", "2", "3"]);
    let (some, exhausted) = p.solve_with("n X", Some(2), None).unwrap();
    assert_eq!(some.len(), 2);
    assert!(!exhausted);
}

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Errors are reported, not raised through C]]
#[test]
fn failure_is_not_an_error() {
    let p = Program::new("pred q o:int.\nq 1.").unwrap();
    assert!(!p.ask("q 2").unwrap());
}

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Assertion is persistent]]
#[test]
fn assert_is_persistent() {
    let p = Program::new("pred q o:int.\nq 1.").unwrap();
    let p2 = p.assert_clause("q 2.").unwrap();
    assert_eq!(p.solve("q X").unwrap().len(), 1);
    assert_eq!(p2.solve("q X").unwrap().len(), 2);
}

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Errors are reported, not raised through C]]
#[test]
fn errors() {
    assert!(Program::new("pred q o:int.\nq foo bar.").is_err());
    assert!(Program::new(APP).unwrap().solve("nope X").is_err());
}

// @tg: verifies:: [[openspec:language-bindings#Rust binding#Shared across threads]]
#[test]
fn threads_share_a_program() {
    let p = std::sync::Arc::new(Program::new(APP).unwrap());
    let hs: Vec<_> = (0..4)
        .map(|i| {
            let p = p.clone();
            std::thread::spawn(move || p.first(&format!("app [{i}] [9] R")).unwrap().unwrap().bindings["R"].clone())
        })
        .collect();
    for (i, h) in hs.into_iter().enumerate() {
        assert_eq!(h.join().unwrap(), format!("[{i}, 9]"));
    }
}

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Handles are distinct under concurrency]]
#[test]
fn concurrent_loads_get_their_own_programs() {
    let hs: Vec<_> = (0..8)
        .map(|i| {
            std::thread::spawn(move || {
                let p = Program::new(&format!("pred v o:int.\nv {i}.")).unwrap();
                p.first("v X").unwrap().unwrap().bindings["X"].clone()
            })
        })
        .collect();
    for (i, h) in hs.into_iter().enumerate() {
        assert_eq!(h.join().unwrap(), i.to_string());
    }
}
