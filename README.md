# agda-ist-algebra
Agda proofs accompanying my PhD thesis, "Development of Algebra in Internal Set Theory".

## Abstract

This thesis explores two novel algebraic applications of Internal Set Theory (IST).
We propose an explicitly topological formalism of structural approximation of groups, generalizing previous work by Gordon and Zilber.
Using the new formalism, we prove that every profinite group admits a finite approximation in the sense of Zilber.
Our main result states that well-behaved actions of the approximating group on a compact manifold give rise to similarly well-behaved
actions of periodic subgroups of the approximated group on the same manifold.
The theorem generalizes earlier results on discrete circle actions, and gives partial non-approximability results for SO(3).
Motivated by the extraction of computational bounds from proofs in a *pure* fragment of IST (Sanders), 
we devise a *pure* presentation of sheaves over topological spaces in the style of Robinson and prove it equivalent to the usual 
definition over standard objects.
We introduce a non-standard extension of Martin-Löf Type Theory with a hierarchy of universes for external propositions along with an
external standardness predicate, allowing us to computer-verify our main result using the Agda proof assistant.

## Highlights

* A proof of the principle of external induction: if an external predicate `P` holds for zero, and `P(k)` implies `P(k+1)` for any standard natural `k`, then `P` holds for every standard natural. [Naturals.agda](src/Naturals.agda) 
* A proof that every standard metric space is an equivalence space (i.e. it admits a proximity predicate that is reflexive, symmetric and transitive). [PredicatedTopologies.agda](src/PredicatedTopologies.agda)
* The proof of the main result (action extension). [MainTheorem.agda](src/Results/MainTheorem.agda)

## Links

[Full text of the thesis](https://www.research.manchester.ac.uk/portal/en/theses/development-of-group-theory-in-the-language-of-internal-set-theory(2f333784-a511-4c85-a7e2-812cc14e6067).html)

