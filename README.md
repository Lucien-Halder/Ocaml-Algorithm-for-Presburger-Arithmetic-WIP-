# An Ocaml algorithm to decide formulas of Presburger Arithmetic
Algorithm :

Let F be a first-order formula for the Presburger arithmetic

1) Put F on Prenex Normal Form (PNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F2

2) Put F2 on Negation Normal Form (NNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F3

3) Normalize F3 to use < as the only comparison operator, yielding

Q1 x1, Q2 x2, ... , Qn xn, F4

4) Put F4 on Conjunctive Normal Form (CNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F5

5) Reorder quantifiers to obtain a conjunction of first-order formulas.

F is now a conjunction of disjunctions of formulas under the form

Q1 x1, Q2 x2, ... , Qr xr, t1(x1,...,xr)<t2(x1,...,xr)

6) Replace every "Forall xi" with "Not(Exists xi, Not(...))"

7) Verify this formula using automata

-----------------------------------------------------------------------

Through simple manipulations of the original formula, this algorithm
uses the classical method with automata, but the automaton is built
only using the < automaton.
With Step 5), eventually, instead of considering the original formula, we
consider a conjunction of simpler formulas.

For now, the only relations this program treats are =,!=,<,<=,>,>=
