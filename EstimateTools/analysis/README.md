# Partial translation of _Analysis I_ into Lean

The files in this directory contain a partial translation of selected portions of my text _Analysis I_ into Lean. The translation is intended to be as faithful as possible to the original text, while also showcasing Lean's features and syntax.  In particular, the formalization is _not_ optimized for efficiency, and in some cases may deviate from idiomatic Lean usage.

Portions of the text that were left as exercises to the reader are rendered in this translation as `sorry`s.  Readers are welcome to fork the repository here to try their hand at these exercises, but I do not intend to place solutions in this repository directly.

Currently formalized sections:

- [Section 2.1: The Peano axioms](./Section_2_1.lean)
- [Section 2.2: Addition](./Section_2_2.lean)
- [Section 2.3: Multiplication](./Section_2_3.lean)