A naive formalization of BLmf using Isabelle. I've submitted this project as the "creative homework" for course [Semantics](https://www21.in.tum.de/teaching/semantics/WS23/index.html) in winter semester 2023 at TUM. As a homework project with a hard deadline, I did not make much effort to make the code concise and robust. The original "readme", as part of the homework, is as following:

---

This is a preliminary formalization of the language BLmf (Bounded Lattices with monotone unary functions) as described in the following conference paper:
Cantone, D., Zarba, C.G. (2006). A Decision Procedure for Monotone Functions over Bounded and Complete Lattices. In: de Swart, H., Orłowska, E., Schmidt, G., Roubens, M. (eds) Theory and Applications of Relational Structures as Knowledge Instruments II. Lecture Notes in Computer Science(), vol 4342. Springer, Berlin, Heidelberg. https://doi.org/10.1007/11964810_15

**Files:**

1. Defs.thy

  Contains the definition of the syntax and semantics of BLmf, based on section 2.4 and 2.5 of the cited paper.
  The definition of semantics has utilized "HOL-Algebra.Lattice", stipulating that in a valid evaluation, the parameter L must satisfy the conditions of a bounded lattice (bounded_lattice L).

2. HelperLemmata.thy

  Lemmata used in the proofs of BLmf rules (BLmfRules.thy), as well as the formalization of Example 25 in the paper (Example.thy).

3. BLmfRules.thy

  The proofs for most of the inference rules described in Fig.1, section 3 of the paper, to be used in the decision procedure. It comprises 2 =-rules, 5 <=-rules, 2 Join-rules, 2 Meet-rules, and 5 Functions rules.
  The second =-rule (If two terms x and y are equal, then within an atom, replacing x with y does not change the value of the atom) is divided into 6 different rules, depending on the type of the input terms (variables or the constants 0/1).

4. Example.thy

  The formalization of an example of the decision procedure of whether the given normalized set of BLmf-literals is satisfiable. The example, and the concrete decision procedure, are found in Example 25 of the paper.