import pytest

from leanelpi import ElpiError, Program, version

APP = """
pred app i:list int, i:list int, o:list int.
app [] L L.
app [X|Xs] L [X|R] :- app Xs L R.
"""


# @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Load and query]]
def test_version():
    assert version().count(".") == 2


# @tg: verifies:: [[openspec:language-bindings#Python binding#Query from Python]]
def test_first_solution():
    assert Program(APP).first("app [1,2] [3] R") == {"R": "[1, 2, 3]"}


# @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Limit stops the search]]
def test_all_solutions_and_limit():
    p = Program("pred n o:int.\nn 1.\nn 2.\nn 3.")
    assert [s["X"] for s in p.solve("n X")] == ["1", "2", "3"]
    sols, exhausted = p.solve_all("n X", limit=2)
    assert len(sols) == 2 and not exhausted


# @tg: verifies:: [[openspec:language-bindings#Python binding#Python failure and errors]]
def test_failure_is_empty_not_an_error():
    p = Program("pred q o:int.\nq 1.")
    assert p.first("q 2") is None and not p.ask("q 2")


# @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Assertion is persistent]]
def test_assert_is_persistent():
    p = Program("pred q o:int.\nq 1.")
    p2 = p.assert_clause("q 2.")
    assert [s["X"] for s in p.solve("q X")] == ["1"]
    assert [s["X"] for s in p2.solve("q X")] == ["1", "2"]


# @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Errors are reported, not raised through C]]
def test_errors():
    with pytest.raises(ElpiError):
        Program("pred q o:int.\nq foo bar.")
    with pytest.raises(ElpiError):
        Program(APP).solve("nope X")


# @tg: verifies:: [[openspec:language-bindings#Python binding#Closed program]]
def test_closed_program():
    p = Program(APP)
    p.close()
    with pytest.raises(ValueError):
        p.first("app [] [] R")
