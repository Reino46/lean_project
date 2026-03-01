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

/- προς αποδειξη του p → q → p ∧ q -/

/-
  And.intro h1 h2 χτιζει αποδειξη του p ∧ q
  χρησιμοποιωντας αποδειξης h1 : p και h2 : q
  ειναι το AND-INTRODUCTION RULE
-/

variable (p q : Prop)
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

-- example = θεωρημα χωρις ονομα και αποθηκευση

/-
  And.left h (και And.right h)
  δημιουργουν αποδειξη του p (αντιστοιχα του q)
  απο αποδειξη h : p ∧ q
  LEFT AND RIGHT-ELIMINATION RULES
-/

variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

-- τοτε εχουμε p ∧ q → q ∧ p:

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

/-
  ∧ ~ × μεσω CURRY - HOWARD
  ∧ για Props (And)
  × για Types (Prod)
-/


/-
  ⟨hp, hq⟩ αντι για And.intro hp hq
-/

variable (p q :Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)


variable (xs : List Nat)
#check List.length xs
#check xs.length
-- μια συντομογραφια

-- αρα η παραπανω αποδειξη γραφεται
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

-- ή ακομα μπορω να κανω flatten nested constructors ωστε ΤΑΕΙ
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

end Kef331

------------------------------- 3.3.2. DISJUNCTION ------------------------------------

namespace Kef332

/-
  Or.intro_left q hp κατασκευαζει αποδειξη του p ∨ q
  απο αποδειξη hp : p
  ομοια Or.intro_right p hq
  LEFT AND RIGHT OR-INTRODUCTION RULES
-/

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

/-
  Για το OR-ELIMINATION RULE:
  μπορω να αποδειξω το r απο το p ∨ q
  αποδεικνυοντας οτι p → r και οτι q → r
-/

/-
  Στην εκφραση Or.elim hpq hpr hqr
  το Or.elim δεχεται 3 συνιστωσες hpq : p ∨ q, hpr : p → r, hqr : q → r
  και δινει μια αποδειξη του r
-/

-- θδο p ∨ q → q ∨ r

variable (q p r : Prop)

#check Or.elim

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
/-
  Απόδειξη p ∨ q → q ∨ p μέσω Ανάλυσης Περιπτώσεων (Or.elim).
  Εξετάζουμε ξεχωριστά την περίπτωση του p και την περίπτωση του q,
  χρησιμοποιώντας τους κανόνες εισαγωγής (intro_left/right) για να χτίσουμε τον στόχο.
-/

-- και με συντομογραφιες:
example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

end Kef332


-------------------------- 3.3.3 NEGATION AND FALSITY --------------------------------

namespace Kef333

-- ¬p οριζεται ως p → False

-- η εκφραση hnp hp παραγει μια αποδειξη του False απο hp : p και hnp : ¬p

-- θδο (p → q) → ¬q → ¬p
variable (p q : Prop)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

/-
  False.elim εκφραζει οτι τα παντα αποδεικνυονται αν εχω contradiction
-/

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
-- το q οτιδηποτε:
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- θδο ¬p → q → (q → p) → r
variable (p q r : Prop)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

/-
  το False εχει ΜΟΝΟ ELIMINATION RULE
  το True εχει ΜΟΝΟ INTRODUCTION RULE, True.intro
  δηλ. το True ειναι απλα αληθεια και εχει κανονικη αποδειξη, την True.intro
-/

end Kef333


----------------------------- 3.3.4. LOGICAL EQUIVALENCE -------------------------------

namespace Kef334

/-
  Η εκφραση Iff.intro h1 h2
  παραγει μια αποδειξη του p ↔ q
  απο h1 : p → q
  και h2 : q → p
-/

/-
  H εκφραση Iff.mp h
  παραγει μια αποδειξη του p → q
  απο το h : p ↔ q
-/

/-
  Αντιστοιχα η Iff.mpr h
  παραγει μια αποδειξη του q → p
  απο το h : p ↔ q
-/

-- θδο p ∧ q ↔ q ∧ p
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

/-
  and_swap: Απόδειξη της μεταθετικότητας του "∧" (And).
  Iff.intro: Ο κανόνας εισαγωγής για το "↔". Απαιτεί δύο αποδείξεις (P → Q και Q → P).
  Iff.mp (modus ponens): Χρησιμοποιεί την ισοδυναμία για να μετατρέψει μια απόδειξη
     του (p ∧ q) σε απόδειξη του (q ∧ p).
-/

-- παλι μπορω να χρησιμοποιησω συντομογραφιες, αλλα με μπερδευουν γιατι δε μπορω να τα διαβασω καθαρα

end Kef334


-------------------------- 3.4. INTRODUCING AUXILIARY SUBGOALS -------------------------

namespace Kef34

/-
  Οταν εχω μεγαλες αποδειξεις, τις σπαω σε μικροτερα κομματια
  δηλ, με το have δημιουργω νεο ΠΡΟΣΩΡΙΝΟ ΥΠΟΣΤΟΧΟ
-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
