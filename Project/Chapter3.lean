-------------------- 3.1. PROPOSITIONS AS TYPES ------------------------

namespace Kef31

-- Prop = type για προτασεις
-- constructors → new propositions

def Implies (p q : Prop) : Prop := p → q
#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check p → q
#check Implies (And p q) (And q p)

-- εισαγω τυπο Proof p για καθε στοιχειο p : Prop

structure Proof (p : Prop) : Type where
  proof : p

#check Proof  -- εχει τυπο Type, οχι Prop

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_commut
-- το "axiom" ειναι μια σταθερα τετοιων τυπων

/- old proofs → new proofs -/
/- Modus Ponens: From a proof of Implies p q and a proof of p,
we obtain a proof of q. -/
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q

/- Suppose that, assuming p as a hypothesis, we have a proof of q.
Then we can “cancel” the hypothesis and obtain a proof of Implies p q. -/
-- αυτο το γραφω:
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies q p)

/-
  για να δω αν η ΕΚΦΡΑΣΗ t ειναι μια σωστη αποδειξη της
  ΔΗΛΩΣΗΣ/ΙΣΧΥΡΙΣΜΟΥ p αρκει να τσεκαρω οτι η t εχει τυπο Proof p
-/

/-
  Proof p = p απλοποιηση
  p ειναι ο τυπος των αποδειξεων του p
  ΑΡΑ ΔΙΑΒΑΖΩ ΤΟ "t : p" ως "Το t αποδειξη του p"
-/

/-
  αρα εχω "Implies p q" = "p → q"
  CURRY - HOWARD ISOMORPHISM ?
  Prop = Sort 0
  Type u = Sort(u+1)
  Prop : κλειστο ως προς το "→" , δηλ.
  αν p q : Prop τοτε p → q : Prop
-/

/-
  Propositions as Types: Μια πρόταση P είναι αληθής αν ο τύπος της "κατοικείται" από έναν όρο (απόδειξη).
  Λόγω του Proof Irrelevance, όλες οι αποδείξεις της ίδιας πρότασης θεωρούνται οριστικά ίσες,
  καθώς μας ενδιαφέρει μόνο η ύπαρξη της απόδειξης και όχι η δομή της.
-/

/-
  Δηλαδη:
  Προταση p = τυπος (Type)
  Αποδειξη t = Στοιχειο του τυπου (Term)
  Αληθεια = Ο τυπος ειναι μη κενος
-/

end Kef31


--------------- 3.2. WORKING WITH PROPOSITIONS AS TYPES ---------------------

set_option linter.unusedVariables false

namespace Kef32

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

-- το #print δινει την αποδειξη ενος θεωρηματος
#print t1

/-
  fun hp : p => ... (λ-αφαιρεση)
  σημαινει εστω μια συναρτηση που δεχεται εισοδο τυπου p
  ή σε γλωσσα λογικης:
  Εστω οτι η προταση p ισχυει (δηλ. εχω μια αποδειξη hp για αυτην)
-/

theorem t1' : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

/-
  Η εντολή `show` δεν αλλάζει τον κώδικα, αλλά λειτουργεί ως "ετικέτα" που δηλώνει
  ρητά ποια πρόταση αποδεικνύουμε σε κάθε βήμα για λόγους σαφήνειας.
-/

-- ή αλλιως:
theorem t1'' (hp : p) (hq : q) : p := hp

-- μπορω να χρησιμοποιησω το t1 σαν function application
axiom hp : p

theorem t2 : q → p := t1 hp

/-
  το 'axiom' δηλωνει την υπαρξη στοιχειου με δοσμενο τυπο
  και μπορει να χαλασει τη λογικη συνεπεια
  π.χ. μπορω να δηλωσω οτι ο κενος τυπος False εχει ενα στοιχειο:
-/
axiom unsound : False
--everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

#print t1''
-- δηλ. για καθε ζευγος προτασεων p, q εχουμε οτι p → q → p

variable {p q : Prop}
theorem t1''' : p → q → p := fun (hp : p) (hq : q) => hp
-- 1. αν δηλωσω τις p, q σαν variables το Lean τις γενικευει για μας
-- 2. αν γενικευσω το t1 ετσι, μπορω να το εφαρμοσω για διαφορετικα ζευγη προτασεων
-- ωστε να παρω διαφορετικες περιπτωσεις του γενικου θεωρηματος:

end Kef32

namespace Kef32'

theorem t1 (p q : Prop) (hp : p) (hq : q) :p := hp

variable (p q r s : Prop)
#check t1 p q
#check t1 r s
#check t1 (r → s) (s → r)

variable (h : r → s)
#check t1 (r → s) (s → r) h
-- η μτβ. h με τυπο r → s, ειναι η υποθεση οτι η r → s ισχυει


-- Θα δω το παραδειγμα της συνθεσης συναρτησεων:
variable (p q r s : Prop)
theorem t2 (h1 : q → r) (h2 : p → q) : p → r :=
  fun h3 : p =>
  show r from h1 (h2 h3)
/-
  σαν θεωρημα της Προτασιακης Λογικης ειναι ο ΥΠΟΘΕΤΙΚΟΣ ΣΥΛΛΟΓΙΣΜΟΣ (ΜΕΤΑΒΑΤΙΚΟΤΗΤΑ)
  δηλ. αν εχω : p → q (h₂)
            και q → r (h₁)
      τοτε εχω p → r
  ΔΟΜΙΚΑ ειναι η συνθεση συναρτησεων εφαρμοσμενη σε ΑΠΟΔΕΙΞΕΙΣ.
-/


-- μπορω να γραψω \0, \1, ... για δεικτες: h₁ h₂ ...

end Kef32'


---------------------- 3.3. PROPOSITIONAL LOGIC --------------------------


namespace Kef33

/-
  Εχουμε:
  Not : ¬ (\not)
  And : ∧ (\and)
  Or : ∨ (\or)
  To : → (\r ή \to)
  Iff : ↔ (\iff)
  ΟΛΑ ΠΑΙΡΝΟΥΝ ΤΙΜΕΣ ΣΤΟ Prop
-/

variable (p q : Prop)
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

/-
  ORDER: ¬ > ∧ > ∨ > → > ↔
  πχ. a ∧ b → c ∨ d ∧ e
  σημαινει (a ∧ b) → (c ∨ (d ∧ e))
-/

/-
  Επισης, p → q → r
  σημαινει "αν π, μετα αν q, τοτε r"
-/


/-
  INTRODUCTION RULES vs ELIMINATION RULES:
  (πως φτιαχνω αποδειξη) vs (πως χρησιμοποιω αποδειξη)
-/

end Kef33


------------------------ 3.3.1. CONJUCTION -----------------------------


namespace Kef331
