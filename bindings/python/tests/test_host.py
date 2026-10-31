"""Host predicates: ELPI calls answered by Python during `Program.solve_host`."""

import threading

import pytest

from leanelpi import App, Const, ElpiError, HostRun, Opaque, Program, Var

GRAPH = """
kind node type.
type a, b, c, d, x, y node.
pred edge i:node, o:node.
pred path i:node, o:node.
path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.
"""

EDGES = [("a", "b"), ("b", "c"), ("c", "d"), ("x", "y")]


def graph() -> Program:
    return Program(GRAPH).declare("pred edge i:node, o:node.")


def edges_from(src: Const):
    return [Const(t) for f, t in EDGES if f == src.name]


# @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host predicate answers a recursive query]]
def test_host_predicate_answers_a_recursive_query():
    p = graph()
    calls = []

    def edge(src):
        calls.append(src.name)
        return edges_from(src)

    run = p.solve_host_all("path a X", {"edge": edge})
    assert isinstance(run, HostRun)
    assert [s.terms["X"] for s in run.solutions] == [Const("b"), Const("c"), Const("d")]
    assert run.solutions[0]["X"] == "b"
    assert run.exhausted and run.fuel_used > 0
    # each clause of path calls edge once: one callback per call, with the input only
    assert calls == ["a", "a", "b", "b", "c", "c", "d", "d"]


def test_rows_zero_one_many():
    p = graph()
    assert p.solve_host("edge a X", {"edge": lambda s: []}) == []        # no rows: failure
    assert p.solve_host("edge a X", {"edge": lambda s: None}) == []
    one = p.solve_host("edge a X", {"edge": lambda s: [(Const("b"),)]})
    assert [s.terms["X"] for s in one] == [Const("b")]
    many = p.solve_host("edge a X", {"edge": lambda s: [Const("b"), Const("c"), Const("d")]})
    assert [s["X"] for s in many] == ["b", "c", "d"]
    # a generator is an iterable of rows too
    gen = p.solve_host("edge a X", {"edge": lambda s: (Const(n) for n in "bc")})
    assert [s["X"] for s in gen] == ["b", "c"]
    # a bound output argument is unified with each row
    assert len(p.solve_host("edge a c", {"edge": lambda s: [Const("b"), Const("c")]})) == 1


def test_raw_host_function_sees_every_argument():
    p = graph()
    seen = []

    def host(name, args):
        seen.append((name, args))
        return edges_from(args[0])

    assert [s["X"] for s in p.solve_host("edge a X", host)] == ["b"]
    name, args = seen[0]
    assert name == "edge" and args[0] == Const("a") and isinstance(args[1], Var)


def test_predicate_with_only_inputs():
    p = Program("pred small i:int.\npred ok i:int.\nok N :- small N, N > 0.").declare(
        "pred small i:int.")
    host = {"small": lambda n: n < 10}  # True: one row without outputs
    assert p.solve_host("ok 3", host) and not p.solve_host("ok 30", host)
    assert not p.solve_host("ok 0", host)  # the rule still checks N > 0


def test_limit_and_fuel():
    p = graph()
    run = p.solve_host_all("path a X", {"edge": edges_from}, limit=1)
    assert len(run.solutions) == 1 and not run.exhausted
    first = p.first_host("path a X", {"edge": edges_from})
    assert first is not None and first.terms["X"] == Const("b")
    assert p.first_host("path y X", {"edge": edges_from}) is None

    loop = Program("pred loop i:int.\nloop N :- loop N.").declare("pred tick o:int.")
    with pytest.raises(ElpiError) as e:
        loop.solve_host("loop 1", {"tick": lambda: []}, fuel=1000)
    assert e.value.out_of_fuel
    run = loop.solve_host_all("tick X", {"tick": lambda: [1]}, fuel=1000)
    assert run.solutions[0].terms["X"] == 1 and 0 < run.fuel_used <= 1000


# @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Panics do not cross the boundary]]
def test_exception_in_callback_becomes_elpi_error():
    p = graph()

    def broken(src):
        raise RuntimeError("table is offline")

    with pytest.raises(ElpiError) as e:
        p.solve_host("path a X", {"edge": broken})
    assert "table is offline" in str(e.value) and "edge" in str(e.value)
    assert isinstance(e.value.__cause__, RuntimeError)
    assert not e.value.out_of_fuel
    # the runtime is still usable
    assert len(p.solve_host("path x X", {"edge": edges_from})) == 1

    def interrupted(src):
        raise KeyboardInterrupt

    with pytest.raises(KeyboardInterrupt):  # re-raised as it is, after the run stops
        p.solve_host("path a X", {"edge": interrupted})
    assert len(p.solve_host("path x X", {"edge": edges_from})) == 1


# @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host errors are reported]]
def test_bad_answers_are_errors():
    p = graph()
    with pytest.raises(ElpiError, match="nowhere"):            # a constant the program lacks
        p.solve_host("path a X", {"edge": lambda s: [Const("nowhere")]})
    with pytest.raises(ElpiError, match="expected 1"):          # a row of the wrong length
        p.solve_host("path a X", {"edge": lambda s: [(Const("b"), Const("c"))]})
    with pytest.raises(ElpiError, match="no host function"):    # no function for the name
        p.solve_host("path a X", {})
    with pytest.raises(ElpiError, match="iterable of rows"):    # a bare value, not rows
        p.solve_host("path a X", {"edge": lambda s: Const("b")})
    with pytest.raises(ElpiError, match="cannot return"):       # a Var may not be returned
        p.solve_host("path a X", {"edge": lambda s: [Var("Q")]})
    # Python values that cannot have the declared type (the engine does not check these)
    with pytest.raises(ElpiError, match="has type node"):
        p.solve_host("path a X", {"edge": lambda s: ["b"]})
    # an unknown name or a clash is a declaration error
    with pytest.raises(ElpiError):
        Program(GRAPH).declare("pred other o:int.", name="edge")
    with pytest.raises(ElpiError):
        Program(GRAPH).declare("pred path i:node, o:node.")


# @tg: verifies:: [[openspec:language-bindings#Host callback predicates#Host predicate without a host]]
def test_declared_predicate_via_plain_solve_errors():
    with pytest.raises(ElpiError, match="host"):
        graph().solve("path a X")
    # the program declare was called on is unchanged
    assert Program(GRAPH).solve("path a X") == []


def test_declare_is_persistent_and_survives_assert():
    base = Program(GRAPH + "\npred twice i:node, o:node.")
    p = base.declare("pred edge i:node, o:node.")
    p2 = p.assert_clause("twice X Z :- edge X Y, edge Y Z.")
    assert [s["Z"] for s in p2.solve_host("twice a Z", {"edge": edges_from})] == ["c"]
    assert base.solve("twice a Z") == []                  # no clauses, no host: plain failure


# @tg: verifies:: [[openspec:language-bindings#Structured answers#Terms decode by kind]]
def test_structured_terms():
    p = Program(
        'kind pt type.\ntype pt int -> string -> pt.\n'
        'pred v o:int, o:string, o:pt, o:list int, o:float.\n'
        'v 42 "hi" (pt 1 "x") [1, 2] 1.5.')
    s = p.solve("v I S P L F")[0]
    assert s.terms == {"I": 42, "S": "hi", "P": App("pt", (1, "x")), "L": [1, 2], "F": 1.5}
    assert s.bindings["P"] == 'pt 1 "x"'           # the printed form is unchanged

    s = Program("pred id o:(int -> int).\nid (x\\ x).").solve("id F, G = G")[0]
    assert isinstance(s.terms["F"], Opaque) and "\\" in s.terms["F"].printed
    assert isinstance(s.terms["G"], Var)
    tail = Program("pred t o:list int.\nt [1|_].").solve("t L")[0].terms["L"]
    assert isinstance(tail, App) and tail.name == "::" and tail.args[0] == 1

    # terms a host returns reach the program intact
    h = p.declare("pred mk o:pt, o:float, o:list int, o:list string.")
    run = h.solve_host_all("mk P F L S", {"mk": lambda: [(App("pt", [7, "q"]), 2, [3], ("u", "w"))]})
    s = run.solutions[0]
    assert s["P"] == 'pt 7 "q"'
    assert s.terms == {"P": App("pt", (7, "q")), "F": 2.0, "L": [3], "S": ["u", "w"]}


def test_bool_outputs():
    p = Program("pred same i:string, i:string, o:bool.\n"
                "pred alias i:string, i:string.\nalias A B :- same A B tt.").declare(
        "pred same i:string, i:string, o:bool.")
    host = {"same": lambda a, b: [a.lower() == b.lower()]}
    assert p.solve_host('alias "Anna" "anna"', host)
    assert not p.solve_host('alias "Anna" "Marco"', host)
    assert p.solve_host('same "a" "b" B', host)[0].terms["B"] == Const("ff")


def test_reentrant_and_threaded_calls():
    p = graph()
    counter = Program("pred n o:int.\nn 1.\nn 2.")

    def edge(src):  # a host may call into the engine again
        assert len(counter.solve("n X")) == 2
        return edges_from(src)

    assert len(p.solve_host("path a X", {"edge": edge})) == 3

    g = Program("pred e i:int, o:int.\npred r i:int, o:int.\nr X Y :- e X Y.").declare(
        "pred e i:int, o:int.")
    out = {}

    def run(i):
        out[i] = [s.terms["Y"] for s in g.solve_host(f"r {i} Y", {"e": lambda n: [n, n + 1]})]

    threads = [threading.Thread(target=run, args=(i,)) for i in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert out == {i: [i, i + 1] for i in range(8)}


# Mirrors "Logic for Agents": the rules own the world and the conclusion; an LLM (simulated)
# only maps the words of a message to the world's constants, and ELPI checks what it says.
WORLD = """
kind person type.
type anna, marco person.
kind city type.
type rome, kyiv city.

pred knows i:person, i:person.
knows anna marco.

pred same_person i:string, o:person.

% "A said B knows C" is believable when both names are people of the world who know each other
pred believable i:string, i:string.
believable A B :- same_person A PA, same_person B PB, knows PA PB.
"""

# what a fuzzy matcher (an LLM) might say for each spelling: candidates, best first
LLM = {"Anya": ["anna"], "Ann": ["anna", "marco"], "Marko": ["marco"],
       "Mario": ["maria"], "Roma": ["rome"]}


def same_person(name):
    return [Const(c) for c in LLM.get(name, [])]


def test_book_demo_llm_maps_names_and_elpi_checks():
    agent = Program(WORLD).declare("pred same_person i:string, o:person.")
    host = {"same_person": same_person}

    assert agent.solve_host('believable "Anya" "Marko"', host)       # anna knows marco
    assert not agent.solve_host('believable "Marko" "Anya"', host)   # knows is directed
    assert not agent.solve_host('believable "Bob" "Marko"', host)    # no match, no claim

    # several candidates: ELPI backtracks over them and keeps the ones the rules accept
    # (knows has input modes, so it checks the pair rather than generating it)
    sols = agent.solve_host('same_person "Ann" P, knows P marco', host)
    assert [s.terms["P"] for s in sols] == [Const("anna")]

    # a hallucinated person is not in the world: an error, not a silent answer
    with pytest.raises(ElpiError, match="maria"):
        agent.solve_host('believable "Mario" "Marko"', host)
    # a constant of the wrong kind (a city for a person) is caught by the binding
    with pytest.raises(ElpiError, match="type person"):
        agent.solve_host('believable "Roma" "Marko"', host)
