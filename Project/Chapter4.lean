--------------- 4.1. THE UNIVERSAL QUANTIFIER ------------------------

namespace Kef41

example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

-- η αλλιως:

example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)


-- εκφραζω οτι μια σχεση r ειναι μεταβατικη:

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

-- βαλε {} για να εννοουνται:

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc


-- παραδειγμα συλλογισμου με σχεση ισοδυναμιας:
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

/-
  ΒΑΣΙΚΟΣ ΚΑΝΟΝΑΣ imax & IMPREDICATIVITY:
    ⋆ Αν η εξοδος μιας συναρτησης ειναι Prop,
    ΤΟΤΕ ΟΛΗ Η ΣΥΝΑΡΤΗΣΗ ειναι Prop, οσο τεραστιο κι αν ειναι το α.
    ⋆ Αυτο καθιστα το Prop 'impredicative':
    επιτρεπει στο ∀ να ποσοδεικτει πανω στο ιδιο το Prop με ασφαλεια.
    ⋆ Ετσι τα μαθηματικα στο Lean δεν καταρρεουν απο παραδοξα,
    ενω τα δεδομενα (Type) παραμενουν 'predicative'.
-/

end Kef41


----------- ** EXERCISES ** --------------

-- EXC 1: Νδ τα ακολουθα

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun hpq : ∀ x, p x ∧ q x =>
    And.intro
      (fun x : α =>
        show (p x) from (hpq x).left )
      (fun x : α =>
        show (q x) from (hpq x).right))
  (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
    have hp : ∀ x, p x := h.left
    have hq : ∀ x, q x := h.right
    fun x : α =>
    show p x ∧ q x from ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq : ∀ x, p x → q x =>
    fun hp : ∀ x, p x =>
      fun x : α =>
        show q x from hpq x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hpq : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x : α =>
      Or.elim hpq
      (fun hp : ∀ x, p x =>
        show p x ∨ q x from Or.inl (hp x))
      (fun hq : ∀ x, q x =>
        show p x ∨ q x from Or.inr (hq x))
