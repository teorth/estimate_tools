import Mathlib.Tactic

/-!
# Analysis I, Section 3.1

In this section we set up a version of set theory that tries to be as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of  the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main results of this section:

- A type `Chapter3.Set` of sets
- A type `Chapter3.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The axioms of the empty set `∅`, singletons `{y}`, and pairs `{y,z}`
- The axiom of pairwise union `X ∪ Y`
- The axiom of specification for subsets `A.specify P` of a set `A` and a predicate `P: (x:Chapter3.Object) → (h:x ∈ A) → Prop`.  TODO: somehow implement set builder elaboration for this.

Some technical notes:
- Mathlib of course has its own notion of a `Set`, which is not compatible with the notion `Chapter3.Set` defined here, though we will try to make the notations match as much as possible.  This causes some notational conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just `∅` to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set` and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion `X.toObject` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is mostly needed when manipulating sets of sets.
- After this chapter is concluded, the notion of a `Chapter3.Set` will be deprecated in favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set in a given type `X`).  However, due to various technical incompatibilities between set theory and type theory, we will not attempt to create any sort of equivalence between these two notions of sets.  (As such, this makes this entire chapter optional from the point of view of the rest of the book, though we retain it for pedagogical purposes.)
-/


namespace Chapter3

structure Set where
  val:Type  -- dummy data

structure Object where
  val:Type  -- dummy data

class SetTheory where
  set_to_object : Set ↪ Object
  mem : Object → Set → Prop
  emptyset: Set
  emptyset_mem x : ¬ mem x emptyset
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y
  singleton : Object → Set
  singleton_axiom x y : mem x (singleton y) ↔ x = y
  union_pair : Set → Set → Set
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y)
  specify A (P: Subtype (fun x:Object ↦ mem x A) → Prop) : Set
  specification_axiom A (P: Subtype (fun x:Object ↦ mem x A) → Prop) :
(∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x


variable [SetTheory]


/-- Definition 3.1.1 (objects can be elements of sets) -/
instance objects_mem_sets : Membership Object Set where
  mem := fun X x ↦ SetTheory.mem x X

/-- Axiom 3.1 (Sets are objects)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

abbrev Set.toObject (X:Set) : Object := X

theorem Set.coe_eq {X Y:Set} (h: X.toObject = Y.toObject) : X = Y := SetTheory.set_to_object.inj' h

@[simp]
theorem Set.coe_eq_iff (X Y:Set) : X.toObject = Y.toObject ↔  X = Y := by
  constructor
  . exact Set.coe_eq
  intro h; subst h; rfl

/-- Axiom 3.2 (Equality of sets)-/
abbrev Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

theorem Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . intro h; apply Set.ext; exact h

instance Set.empty_inst : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

/-- Axiom 3.3 (empty set).  Note: one may have to explicitly cast ∅ to Set due to Mathlib's existing set theory notation. -/
theorem Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Empty set is unique -/
theorem Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, ¬ x ∈ X) := by
  sorry

theorem Set.empty_unique : ∃! (X:Set), ∀ x, ¬ x ∈ X := by
  sorry

/-- Lemma 3.1.5 (Single choice) -/
lemma Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, Set.not_mem_empty]
  replace claim := Set.ext claim
  contradiction

instance Set.singleton_inst : Singleton Object Set where
  singleton := SetTheory.singleton

/-- Axiom 3.3(a) (singleton).  Note one may have to explicitly cast {a} to Set due to Mathlib's existing set theory notation. -/
theorem Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance Set.union_pair_inst: Union Set where
  union := SetTheory.union_pair

/-- Axiom 3.4 (Pairwise union)-/
theorem Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) := SetTheory.union_pair_axiom X Y x

instance Set.insert_inst : Insert Object Set where
  insert := fun x X ↦ {x} ∪ X

/-- Axiom 3.3(b) (pair).  Note that one often has to cast {a,b} to Set -/
theorem Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

theorem Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  rw [Set.pair_eq, Set.mem_union, Set.mem_singleton, Set.mem_singleton]

/-- Remark 3.1.8 -/
theorem Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by sorry

theorem Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by sorry

theorem Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by sorry

theorem Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  sorry

/-- Exercise 3.1.1 -/
theorem Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) : a = c ∧ b = d ∨ a = d ∧ b = c := by
  sorry

abbrev Set.empty : Set := ∅
abbrev Set.singleton_empty : Set := {Set.empty.toObject}
abbrev Set.pair_empty : Set := {Set.empty.toObject, Set.singleton_empty.toObject }

/-- Exercise 3.1.2-/
theorem Set.emptyset_neq_singleton : Set.empty ≠ Set.singleton_empty := by
  sorry

theorem Set.emptyset_neq_pair : Set.empty ≠ Set.pair_empty := by sorry

theorem Set.singleton_empty_neq_pair : Set.singleton_empty ≠ Set.pair_empty := by
  sorry

/-- Remark 3.1.11.  (These results can be proven either by a direct rewrite, or by using extensionality.) -/
theorem Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by sorry

theorem Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by sorry

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem Set.singleton_union_singleton (a b:Object) : ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  sorry

theorem Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by sorry

theorem Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  apply Set.ext
  intro x
  constructor
  . intro hx
    rw [Set.mem_union] at hx
    rcases hx with case1 | case2
    . rw [Set.mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [Set.mem_union]; tauto
      have : x ∈ B ∪ C := by rw [Set.mem_union]; tauto
      rw [Set.mem_union]; tauto
    have : x ∈ B ∪ C := by rw [Set.mem_union]; tauto
    rw [Set.mem_union]; tauto
  sorry

/-- Proposition 3.1.27(c) -/
theorem Set.union_self (A:Set) : A ∪ A = A := by
  sorry

/-- Proposition 3.1.27(a) -/
theorem Set.union_empty (A:Set) : A ∪ ∅ = A := by
  sorry

/-- Proposition 3.1.27(a) -/
theorem Set.empty_union (A:Set) : ∅ ∪ A = A := by
  sorry

theorem Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem Set.pair_union_pair (a b c:Object) : ({a,b}:Set) ∪ {b,c} = {a,b,c} := sorry

/-- Definition 3.1.14.  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`. -/
instance Set.subset_inst : HasSubset Set where
  Subset := fun X Y ↦ ∀ x, x ∈ X → x ∈ Y

instance Set.strict_subset_inst : HasSSubset Set where
  SSubset := fun X Y ↦ X ⊆ Y ∧ X ≠ Y

theorem Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

theorem Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/

theorem Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by sorry

/-- Examples 3.1.16 -/
theorem Set.subset_self (A:Set) : A ⊆ A := by sorry

theorem Set.empty_subset (A:Set) : ∅ ⊆ A := by sorry

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem Set.subset_trans (A B C:Set) (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- this proof is written to follow the structure of the original text.
  rw [Set.subset_def]
  intro x hx
  rw [Set.subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

theorem Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  sorry

theorem Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  sorry

abbrev Set.toSubtype (A:Set) := Subtype (fun x:Object ↦ x ∈ A)

abbrev Set.specify (A:Set) (P: A.toSubtype → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem Set.specification_axiom {A:Set} {P: A.toSubtype → Prop} {x:Object} (h: x ∈ A.specify P) : x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

theorem Set.specification_axiom' {A:Set} (P: A.toSubtype → Prop) (x:A.toSubtype) : x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

theorem Set.specify_subset {A:Set} (P: A.toSubtype → Prop) : A.specify P ⊆ A := by sorry

/-- This exercise may require some understanding of how  subtypes are implemented in Lean. -/
theorem Set.specify_congr {A A':Set} (hAA':A = A') {P: A.toSubtype → Prop} {P': A'.toSubtype → Prop} (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) : A.specify P = A'.specify P' := by sorry

instance Set.intersection_inst : Inter Set where
  inter := fun X Y ↦ X.specify (fun x ↦ x.val ∈ Y)

/-- Definition 3.1.22 (Intersections) -/
theorem Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := Set.specification_axiom h
    simp [h']
    exact (Set.specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (Set.specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance Set.sdiff_inst : SDiff Set where
  sdiff := fun X Y ↦ X.specify (fun x ↦ x.val ∉ Y)

/-- Definition 3.1.26 (Difference sets) -/
theorem Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := Set.specification_axiom h
    simp [h']
    exact (Set.specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (Set.specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by sorry

/-- Proposition 3.1.27(b) -/
theorem Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by sorry

theorem Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by sorry

/-- Proposition 3.1.27(c) -/
theorem Set.inter_self (A:Set) : A ∩ A = A := by
  sorry

/-- Proposition 3.1.27(e) -/
theorem Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by sorry

/-- Proposition 3.1.27(f) -/
theorem  Set.inter_union_distrib_left (A B C:Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := sorry

theorem  Set.union_inter_distrib_left (A B C:Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := sorry

/-- Proposition 3.1.27(f) -/
theorem Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by sorry

theorem Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by sorry

/-- Proposition 3.1.27(g) -/
theorem Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by sorry

theorem Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by sorry

instance Set.distribLattice_inst : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := Set.subset_self
  le_trans := Set.subset_trans
  le_antisymm := Set.subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by sorry
  le_sup_right := by sorry
  sup_le := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←Set.union_inter_distrib_left]
    exact Set.subset_self _

instance Set.orderBot_inst : OrderBot Set where
  bot := ∅
  bot_le := Set.empty_subset

/-- Definition of disjointness -/
theorem Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff


end Chapter3
