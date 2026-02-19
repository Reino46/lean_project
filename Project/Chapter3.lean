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

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
