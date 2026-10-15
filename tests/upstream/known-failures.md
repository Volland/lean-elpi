# Known failures

Upstream tests that lean-elpi does not pass yet, one `## name` heading each with the first
error lean-elpi reports. The runner reports them as `known` instead of failing, and as `stale`
once they pass. Gaps are debt against the ELPI 1.18 dialect decision, not accepted differences.

## name

lean-elpi: unknown option '-no-tc'

## nil_cons

nil_cons.elpi:1:28: undeclared constant 'cons'

## random

random.elpi:3:2: undeclared constant 'random.int'

## findall

findall.elpi:20:47: undeclared constant 'same_var'

## unix

unix.elpi:35:8: undeclared constant 'std.spy-do!'

## cut2

runs but the query fails (main returns Failure)

## typeabbrv4

typeabbrv4.elpi:6:0: type abbreviation 't1' is already defined

## typeabbrv8

typeabbrv8.elpi:1:20: expected '}' but found '.'

## typeabbrv10

typeabbrv10.elpi:7:16: integer has type int but is used with type (list ?1)

## typeabbrv11

typeabbrv11.elpi:4:2: "x" has type string but is used with type int

## typeabbrv12

typeabbrv12.elpi:4:2: "x" has type string but is used with type (list int)

## conj2

conj2.elpi:4:19: expected ']' but found '&'

## impl2

impl2.elpi:3:42: undeclared constant 'r'

## llam

llam.elpi:41:53: undeclared constant 'f'

## restriction3

restriction3.elpi:2:0: 'mode' is unsupported in this milestone

## notation

notation.elpi:13:0: term expected, found '~'

## pnf

pnf.elpi:86:26: expected ')' but found '\'

## holp

holp/main.mod:19:42: unexpected character '`'

## ndprover

ndprover/inter.mod:23:19: unexpected character '`'

## pcf

pcf/pcf.mod:7:20: expected '.' but found ','

## progs

lean-elpi: unknown option '-delay-problems-outside-pattern-fragment'

## hilbert

lean-elpi: unknown option '-delay-problems-outside-pattern-fragment'

## hilbert2

lean-elpi: unknown option '-delay-problems-outside-pattern-fragment'

## eta_as

lean-elpi: unknown option '-no-tc'

## hdclause

lean-elpi: unknown option '-no-tc'

## namespace00

namespaces00.elpi:9:33: undeclared constant 'aux'

## namespace02

namespaces00.elpi:9:33: undeclared constant 'aux'

## namespace03

namespaces03.elpi:8:12: undeclared constant 'c.foo'

## shorten

shorten.elpi:14:0: 'shorten' is unsupported in this milestone

## shorten-EOF

shorten2.elpi:1:22: expected '.' but found ','

## shorten_trie

shorten_trie.elpi:5:0: 'shorten' is unsupported in this milestone

## shorten_builtin

shorten_builtin.elpi:1:0: 'shorten' is unsupported in this milestone

## discard

discard.elpi:7:7: expected '.' but found '\'

## chr

chr.elpi:6:0: 'mode' is unsupported in this milestone

## chr_leq

chrLEQ.elpi:1:0: 'mode' is unsupported in this milestone

## chr_nokey

chr_nokey.elpi:7:1: 'rule' expected in a constraint block

## chr_gcd

chrGCD.elpi:1:0: 'mode' is unsupported in this milestone

## chr_nokey2

chr_nokey2.elpi:3:42: undeclared constant 'false'

## chr_ut

llamchr.elpi:1:0: 'mode' is unsupported in this milestone

## w

w.elpi:18:7: expected '.' but found '==>'

## uvar_keyword

uvar_chr.elpi:2:9: unknown type 'term'

## impl_order

[a, b, c]

## list_as_conj

list_as_conj.elpi:3:11: application of :: has type (list prop) but is used with type prop

## spilling_lam

spill_lam.elpi:2:25: undeclared constant 'x'

## spilling_impl

spill_impl.elpi:12:24: => is applied to 3 arguments but its type any -> prop -> prop takes 2

## spilling_and

spill_and.elpi:12:24: => is applied to 3 arguments but its type any -> prop -> prop takes 2

## elpi_only_llam

(exit 0, expected failure)

## hollight

hollight.elpi:469:36: unexpected character '''

## asclause

asclause.elpi:5:8: term is applied to 2 arguments but its type int takes 0

## elpi-checker

elpi-checker-copy.elpi:18:6: unexpected character '`'

## elpi2html

elpi2html-copy.elpi:7:0: 'shorten' is unsupported in this milestone

## same_term

same_term.elpi:8:2: pi is applied to 2 arguments but its type (?25 -> prop) -> prop takes 1

## heap_discard

heap_discard.elpi:5:2: pi is applied to 2 arguments but its type (?15 -> prop) -> prop takes 1

## quote_syntax

quote_syntax.elpi:2:2: undeclared constant 'quote_syntax'

## var

var.elpi:7:3: pi is applied to 2 arguments but its type (?7 -> prop) -> prop takes 1

## hyp_uvar

runs but the query fails (main returns Failure)

## variadic_declare_constraints

variadic_declare_constraints.elpi:1:9: unknown type 'tm'

## notation_error

<query>:1:0: undeclared constant 'main'

## printer

lean-elpi: unknown option '-no-tc'

## graft_replace_ok

graft_replace_ok.elpi:5:9: term is applied to 2 arguments but its type string takes 0

## graft_replace_err

graft_replace_err.elpi:6:9: term is applied to 2 arguments but its type string takes 0

## bad_index

bad_index.elpi:2:10: expected '.' but found ':'
