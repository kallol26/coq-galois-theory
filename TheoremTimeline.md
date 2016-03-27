# Definitions #

The first step in the program is to define all the relevant algebraic
structures.  This is not an easy task.  Type theory is not as flexible
as set theory.  The choice of whether to make a structure a type,
or a predicate on elements of a type, is not at all obvious.  We will comment
on our choice of definitions in the code itself, which is linked below.

The columns are
  * Definition:  An english description of the mathematical object being defined
  * Rotman #: The definitions in Rotman are not numbered.  Thus we give the page number where they occur.  If a definition is left out as assumed, we list another source.
  * Done: one of {Yes, No, In Progress}.
  * Coq: a link to the formal statement of the definition in the project source.


| _**Definition**_ | _**Rotman #**_ | _**Done**_ | _**Coq**_ |
|:-----------------|:---------------|:-----------|:----------|
| Rings            | 1              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#Ring) |
| Polynomials      | 2              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly.html#Poly) |
| Leading Coefficient | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#lc) |
| Monic Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#monic) |
| Constant Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#constant) |
| Linear Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#linear) |
| Quadratic Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#quadratic) |
| Cubic Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#cubic) |
| Quartic Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#quartic) |
| Quintic Polynomial | 3              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#quintic) |
| (Integral) Domain | 4              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#Domain) |
| Unit in a Ring   | 5              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#unit) |
| Field            | 6              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#field) |
| Subring          | 6              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#Sub_ring) |
| Subfield         | 6              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#Sub_field) |
| Field of Fractions | 6              | No         | coq       |
| Homomorphism     | 7              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#Homo) |
| Isomorphism      | 7              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#iso) |
| Ideal            | 8              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#Ideal) |
| Kernel           | 9              | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#kernel) |
| Quotient Ring    | 10             | No         | coq       |
| Principle Ideal Domain | 12             | No         | coq       |
| Divides          | 12             | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#pdivides) |
| Greatest Common Divisor | 12             | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/ring.html#gcd) |
| Irreducible Polynomial | 15             | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#irreducible) |
| Prime Ideal      | 17             | No         | coq       |
| Maximal Ideal    | 18             | No         | coq       |
| Splits           | 19             | No         | coq       |
| Prime Field      | 20             | No         | coq       |
| Characteristic of a Field | 20             | No         | coq       |
| Primitive Polynomial | 23             | No         | coq       |
| Content of a Polynomial | 23             | No         | coq       |
| Extension Field  | 28             | No         | coq       |
| Degree of an Extension | 28             | No         | coq       |
| Finite Extension | 28             | No         | coq       |
| Simple Extension | 28             | No         | coq       |
| Algebraic        | 29             | No         | coq       |
| Transcendental   | 29             | No         | coq       |
| Irreducible Polynomial of an Element | 29             | No         | coq       |
| Splitting Field  | 30             | No         | coq       |
| Separable Polynomial | 31             | No         | coq       |
| Galois Field     | 33             | No         | coq       |
| Pure Extension   | 33             | No         | coq       |
| Solvable by Radicals | 34             | No         | coq       |
| Field Automorphism | 35             | No         | coq       |
| Galois Group     | 35             | No         | coq       |
| Transitive Group Action | 37             | No         | coq       |
| Solvable Group   | 37             | No         | coq       |
| Primitive Element | 39             | No         | coq       |
| Frobenius Automorphism | 40             | No         | coq       |
| Character of a Group | 43             | No         | coq       |
| Automorphism Group | 43             | No         | coq       |
| Fixed Field      | 43             | No         | coq       |
| Galois (Normal) Extension | 47             | No         | coq       |
| Lattice          | 48             | No         | coq       |


We may not need all these definitions for the main goal.  For example, I don't know if we'll have
time for finite fields.


# Theorems #

The following table gives a list of theorems we need to prove in Coq
to complete our project.   We follow the text
"Galois Theory" by Joseph Rotman.  (Springer-Verlag, 1991).
The theorem and exercise numbers refer to that text.
The theorems and exercises are numbered with distinct counters,
thus the somewhat unusual ordering in the followign table.

The columns are
  * Rotman #: The number from the text.  When we feel a theorem is left out (e.g. linear algebra theorems that are assumed), or just stated as obvious (such as "polynomials form a ring") we add a theorem with tag Assumed and number it to the closest Rotman theorem number.
  * Done: one of {Yes, No, In Progress}.
  * Coq: a link to the formal statement of the theorem in the project source.
  * Date: the projected date we hope to have the theorem completed by.

| _**Rotman #**_ | _**Brief Description**_| _**Done**_ | _**Coq**_ | _**Date**_ |
|:---------------|:-----------------------|:-----------|:----------|:-----------|
| **Rings**      |                        |            |           |            |
| Theorem 1      |                        | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#mul0r) | 6/1        |
| Assumed 1a     | Polynomials form a ring | **No**     | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#mul0r) | 6/1        |
| Theorem 2      |                        | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/poly2.html#domain_cancel) | 6/1        |
| Exercise 4     |                        | **Yes**    | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 6/1        |
| Exercise 7     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 10    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 11    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 12    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 13    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Homomorphisms and Ideals** |                        |            |           |            |
| Exercise 18    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 19    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 20    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 27    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 29    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 30    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 32    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 33    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Quotient Rings** |                        |            |           |            |
| Theorem 3      |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 37    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 39    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Polynomial Rings over Fields** |                        |            |           |            |
| Theorem 4      |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 5      |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 41    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 6      |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 7      | Euclidean Algorithm    | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 8    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 46    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 9      |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 10   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 11     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Prime Ideals and Maximal Ideals** |                        |            |           |            |
| Exercise 50    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 53    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 12     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 13     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 14   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 15     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 16   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 17     | Kronecker              | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Finite Fields** |                        |            |           |            |
| Theorem 18     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 59    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 19     | Galois                 | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 64    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Irreducible Polynomials** |                        |            |           |            |
| Exercise 66    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 67    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 69    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 70    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 20       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 21       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 22       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 23     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 24     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 25   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 26   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Splitting Fields** |                        |            |           |            |
| Theorem 27     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 73    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 74    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 28     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 29   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 30     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 31       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 32     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 33   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 34   | (E.H. Moore)           | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Solvability by Radicals** |                        |            |           |            |
| Exercise 78    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 79    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 81    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 82    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **The Galois Group** |                        |            |           |            |
| Lemma 35       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 36     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 37     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 83    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Exercise 84    |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 38       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 39     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 40     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Primitive Roots of Unity** |                        |            |           |            |
| Lemma 41       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 42     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 43     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 44     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 45   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 46   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 47       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 48     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 49       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 50     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 51     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 52   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Insolvability of the Quintic** |                        |            |           |            |
| Theorem 53     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 54     | (Abel-Ruffini)         | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Independence of Characters** |                        |            |           |            |
| Lemma 55       | (Dedekind)             | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 56   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 57       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 58     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Corollary 59   |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Galois Extensions** |                        |            |           |            |
| Theorem 60     |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| **Fundamental Theorem of Galois Theory** |                        |            |           |            |
| Lemma 61       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Lemma 62       |                        | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |
| Theorem 63     | Fundamental Theorem of Galois Theory | No         | [coq](http://www.cs.cmu.edu/~seanmcl/software/galois/doc/galois.html#RingThm3) | 8/31       |

We may not this entire list to prove Theorem 63.  We'll learn which we really need by working
backwards.