-----------/- 2.1. SIMPLE TYPE THEORY -/------------------

set_option linter.unusedVariables false
namespace Kef21

/- Defining constants -/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/- Checking their types -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
-- "&&" is the boolean and
#check b1 && b2
-- "||" is the boolean or
#check b1 || b2
-- check δίνει τι αντικείμενο είναι, όχι το αποτέλεσμα της πράξης

-- Boolean "true"
#check true
-- το true (τιμή) είναι τύπου Bool
-- διαφορετικό από το True (τύπου Prop)

/- Evalutating -/

#eval 5*4
#eval n*m
#eval m + 2
#eval b1 && b2
#eval b1 || b2

/- tests -/
def a : Nat := 1
def b : Nat := 2
def c : Nat := 0

#check a
#check a*b + c
#check a^2

#eval a^2
#eval (b^2 + b) * a
#eval (a + b^3 + c)*c

#eval (b1 || b2) && b2
#eval (b1 || b2) || (b1 && b2)

/- if a,b types, then a → b type of functions from a to b-/
/- a × b type of cartesian product -/

/- γραφω \r για βελος και \x για καρτ. γινόμενο -/

#check Nat → Nat
#check Nat -> Nat
-- μπορεις και απλα ->
#check Nat × Nat
#check Prod Nat Nat
-- μπορεις και απλα Prod για γινομενο

#check Nat -> Nat -> Nat
#check Nat -> ( Nat -> Nat )

#check Nat × Nat -> Nat
#check (Nat -> Nat) -> Nat


#check Nat.succ
#check (0,1)
#check Nat.add

#check Nat.succ 2 -- συναρτηση "επομενος" στο 2
-- εχει τυπο Nat -> Nat αρα αν δωσω Nat (2) δινει Nat
#check Nat.add 3 -- τυπου Nat -> Nat -> Nat
-- αρα δινει Nat -> Nat αν δωσω απλα το 3
#check Nat.add 5 2
-- δινει Nat αν δωσω 2 ορισματα
-- δηλ. τον τυπο της τελικης τιμης
#check (5,9).1 --δινει (5,9).fst : Nat
-- δηλ δινει τον τυπο του πρωτου ορου του ζευγους
#check (5,9).2
-- αντιστοιχα του δευτερου


#eval Nat.succ 2
#eval Nat.add 3 5
#eval (5,9).1
#eval (5,9).2

/- Nat → Nat → Nat ισοδυναμει με Nat → (Nat → Nat) -/

end Kef21



------------/- 2.2. TYPES AS OBJECTS -/-----------------

namespace Kef22

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat → Nat × Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat) -- το ιδιο με πανω
#check (Nat → Nat) → Nat  -- διαφορετικο!

-- αυτοι οι τυποι, εχουν επισης τυπο: Type

-- μπορω να φτιαξω καινουριες σταθερες για τυπους:
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check β
#check F α
#check F Nat
#check G α  -- δινει Type → Type
#check G α β -- προφανως δινει απλα Type
#check G α Nat

/- εχω δει ηδη συναρτηση με τυπο Type → Type → Type -/
/- ειναι το καρτ. γινομενο Prod -/
#check Prod α β
#check α × β -- το ιδιο
#check Prod Nat Nat

/- για καθε τυπο α, ο τυπος List α παριστανει τον τυπο
λιστων με στοιχεια τυπου α-/
#check List α
#check List Nat

/- Καθε εκφραση εχει τυπο, αρα τυπο εχει ο Type ? -/
#check Type -- δινει Type 1
#check Type 1 -- δινει Type 2
#check Type 2 -- Type 3
#check Type 3 -- κοκ

/- Type 0: συμπαν μικρων/απλων τυπων -/
/- Τype 1: μεγαλυτερο συμπαν που περιεχει τον Type 0 σαν στοιχειο-/
/- Type 2: ακομα μεγαλυτερο, περιεχει τον Type 1-/
/- Type 0 = Type -/

/- sorts = τυποι των τυπων
πχ sort 0 = Prop
   sort 1 = Type
   sort 2 = Type 1 -/

/- πχ το List α πρεπει να βγαζει νοημα για καθε τυπο α,
ανεξαρτητα απο το ποιο συμπαν ζει ο α -/
#check List -- δινει Type u, u: μεταβλητη
/- δηλαδη οποτε ο α εχει τυπο Type u
και το List α εχει επισης τυπο Type u-/
#check Prod -- ομοια πολυμορφικο


/- μπορω να ορισω μεταβλητες συμπαντος
για να ορισω πολυμορφικες μεταβλητες -/
universe u
def T (α : Type u) : Type u := Prod α α
#check T -- αν α τυπου Type u, τοτε Τ τυπου Type u

/- μπορω να αποφυγω το universe command
οριζοντας τις παραμετρους του συμπαντος οταν οριζω το Τ -/
def T2.{y} (α : Type y) : Type y := Prod α α
#check T2 -- αν α τυπου Type y, τοτε Τ2 τυπου Type y

end Kef22



---------------- 2.3. FUNCTION ABSTRACTION AND EVALUATION ------------


namespace Kef23

/- function from expression: -/
#check fun (x : Nat) => x + 5
#check λ (x: Nat ) => x +5

#check fun x => x+5
#check λ x => x + 5
-- εδω το Nat εννοειται, μπορει να παραλειφθει

#eval (λ x => x + 5) 10
-- αν δωσω τιμη, υπολογιζει

/- lamda abstraction
x:α και κατασκευαζω t:β , τοτε
λ (x : α) => t ειναι αντικειμενο με τυπο α → β
δηλ. συναρτηση απο το α στο β που στελνει
καθε τιμη του x στην τιμη t -/
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2
-- ολα η ιδια εκφραση

/- πραξεις συναρτησεων ως lamda abstraction -/
def f (n: Nat) : String := toString n
def g (s: String) : Bool := s.length > 0

-- τι κανουν αυτες? --
#eval f 32
-- μετατρεπει τον αριθμο σε κειμενο/συμβολοσειρα (string)
#eval g "Lean"
-- ελεγχει αν η συμβολοσειρα ειναι μη κενη
#eval g "" -- πχ εδω δινει false

#check fun x : Nat => x
#check fun x : Nat => true
#check fun x : Nat => Bool
#check fun x : Nat => f x
#check fun x : Nat => g (f x) -- Nat → String → Bool
                              -- αρα Nat → Bool
                              -- ειναι η συνθεση g ∘ f
#check fun x => g (f x) -- το ιδιο
-- γενικα μπορω να παραλειπω τη δηλωση των τυπων


/- μπορω να περασω συναρτησεις ως παραμετρους: -/
#check fun (g: String → Bool) (f: Nat → String) (x: Nat) => g (f x)
/- ή και τυπους ως παραμετρους: -/
#check fun (α β γ : Type) (g: β → γ) (f: α → β) (x : α) => g (f x)

/- γενικη μορφη λ-εκφρασεων ειναι:
fun (x : α) => t , οπου η x : bound variable -/

/- alpha equivalence:
fun (b : β) (x : α) => b
fun (u : β) (z : α) => u -/

/- Αν εφαρμοσω το term  t : α → β στο s : α
θα παρω μια εκφραση t s : β  -/

#check (fun x : Nat => x) 1
#check (fun x : Nat => true) 1

#check (fun (α β γ : Type) (u: β → γ) (v: α → β) (x: α) => u (v x)) Nat String Bool g f 0
-- δεχεται 6 ορισματα: α,β,γ τυπους, συναρτησεις u,v και τιμη x τυπου α
-- παιρνει το x, εφαρμοζει v, εφαρμοζει u
-- δηλ υπολογιζει u(v(x))
-- μετα του δινω τιμες: α=Nat, β=String, γ=Bool, u=g, v=f, x=0
-- τελικα δινει Bool, αφου g(f(0))=τιμη boolean
-- συγκεκριμενα true αφου το "0" εχει μηκος 1>0
-- POLYMORPHIC, HIGHER ORDER

/- προφανως: -/
#eval (fun x : Nat => x) 1
#eval (fun x : Nat => true) 1

end Kef23


-------------- 2.4. DEFINITIONS -----------------


namespace Kef24

def double (x : Nat) : Nat := x + x
#eval double 3
-- def = named fun
def double2 : Nat → Nat := fun x => x + x
#eval double2 3
-- ή παραλειπεις τη δηλωση τυπου:
def double3 := fun (x:Nat) => x + x
#eval double3 3

/- γενικη μορφη def:
def foo : α := bar
οπου foo = ονομα, α = τυπος, bar = τιμη ή ορος (term)
πχ: -/
def pi := 3.141592654
-- και μπορει να παρει παραμετρους:
def add (x y : Nat) := x + y
#eval add 3 2

-- ή αλλιως:
def add2 (x : Nat) (y : Nat) := x + y
#eval add2 3 2

#eval add (double 3) (7 + 9)

def greater (x y : Nat) :=
    if x > y then x
    else y
#eval greater 32 43

-- function as an input:
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
    f (f x)
#eval doTwice double 2

-- more abstract:
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) :γ :=
    g (f x)
    /- δηλαδη η συνθεση παιρνει 2 οποιεσδηποτε συναρτησεις f,g
    αρκει αυτες να δεχονται μονο μια εισοδο η καθεμια,
    με τους καταλληλους τυπους. -/
#check compose

def square (x : Nat) : Nat :=
    x * x
#eval compose Nat Nat Nat double square 3
/- η compose δουλευει για οποιεσδηποτε συναρτησεις αρκει απλα
να δεχονται μια παραμετρο και
ο τυπος του αποτελεσματος της δευτερης
να ειναι ιδιος με τον τυπο της εισοδου της πρωτης
ΓΙΑ ΚΑΘΕ ΤΥΠΟ α, β, γ,-/

end Kef24


------------------- 2.5. LOCAL DEFINITIONS ---------------------


namespace Kef25

/- "Local Definition":    let α : t1; t2
οριζει το αποτελεσμα αντικατασταση του α στο t2, με t1-/
#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y
#eval twice_double 2

/- λεμε οτι οι εκφρασεις
twice_double x  και
(x + x)(x + x)
ειναι definitionally equal -/

-- chain:
#check let y := 2 + 2; let z := y + y; z * z
#eval let y := 2 + 2; let z := y + y; z * z
-- ή πιο απλα (line breaks)
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
#eval t 2
#eval t (t 2)

/- let α := t1; t2
ειναι πολυ κοντα στο
  fun (α => t2) t1
αλλα δεν ειναι το ιδιο.
Η εκφραση α => t2 πρεπει να βγαζει νοημα ΓΙΑ ΚΑΘΕ α)
Αντιπαραδειγμα: -/
def foo := let a := Nat; fun x : a => x + 2
--δουλευει μια χαρα, α συντομογραφια για το Nat,
--κανει αντικατασταση πριν ελεγξει αν η προσθεση ειναι εγκυρη
----- ΕΝΩ ΤΟ -----
/- def bar := (fun a => fun x : a => x + 2) Nat -/
-- δεν δουλευει, α: γενικος τυπος, μπορω να προσθεσω παντα το 2
-- σε ενα x οποιουδηποτε τυπου α? ΟΧΙ
-- πχ α := String ή Bool , το x + 2 δεν βγαζει νοημα

end Kef25


------------------ 2.6. VARIABLES AND SECTIONS -----------------


namespace Kef26

section useful
-- δες τελος κεφαλαιου για sections

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)
def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

-- αλλιως:
variable (α β γ : Type)
def compose2 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def doTwice2 (h : α → α) (x : α) : α :=
  h (h x)
def doThrice2 (h : α → α) (x : α) : α :=
  h (h (h x))

-- ή πιο γενικα:
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose3 := g (f x)
def doTwice3 := h (h x)
def doThrice3 := h (h (h x))

#print compose
#print doTwice
#print doThrice
-- ειναι οι ιδιες συναρτησεις με τηνα ρχη

-- το variable μενει μεχρι το τελος του αρχειου
-- οποτε χρησιμοποιουμε section:
end useful

end Kef26


------------------ 2.7. NAMESPACES ------------------------

-- το χρησιμοποιω ηδη

#check List.nil
#check List.cons
#check List.map
-- μπορω με open:
open List
#check nil
#check cons
#check map
-- και μπορω να τα κανω nested


------------ 2.8. WHAT MAKES DEPENDANT TYPE THEORY DEPENDENT? ------------


namespace Kef28

-- πως θα φτιαξω μια συναρτηση για ολα τα ειδη λιστων?
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check cons Bool
#check cons
-- δηλαδη εχω dependent function type / dependent arrow type

/- ο τυπος (a : α) → β a
παριστανει τον τυπο ολων των συναρτησεων f τ.ω.
για καθε a : α , η f ειναι στοιχειο τυπου β a
ΔΗΛΑΔΗ ΕΞΑΡΤΑΤΑΙ ΑΠΟ ΤΗΝ ΕΙΣΟΔΟ -/

/- (a : α) → β  βγαζει νοημα για καθε β : Type
Αν η τιμη του β εξαρταται απο το a (οπως πριν)
τοτε εχουμε dependent function type ή Π-Types
ΑΝ ΕΙΝΑΙ ΑΝΕΞΑΡΤΗΤΟ ΟΜΩΣ, το
(a : α) → β ειναι το ιδιο με το α → β  -/

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append
-- το @ δειχνει ολα τα ορισματα
-- {...} γιατι το Lean μαντευει

/- Ομοια με το α → β γενικευουμε το καρτεσιανο γινομενο
και παιρνουμε Σ-Types (Dependent Products) -/
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2
-- α = Nat , β = x
-- αρα η f δινει ⟨Nat , x⟩
-- και με το .2 παιρνω το x

#eval h1 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5

-- f , g ειναι ιδιες

end Kef28

-- Π-Types: ΣΥΝΑΡΤΗΣΕΙΣ  (a : α) → β a
-- Σ-Types: ΖΕΥΓΗ        (a : α) × β a



------------------- 2.9. IMPLICIT ARGUMENTS ----------------------


namespace Kef29

-- φτιαχνω δικια μου δομη λιστας
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append

-- then Nat:
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)
#check Lst.append Nat as bs
-- δηλ. σπαμμαρω το Nat (πλεονασμος)

namespace sidequest

-- αντι αυτου βαλε _ :
#check Lst.cons _ 0 (Lst.nil _)

/- def as : Lst _ := Lst.nil _
def bs : Lst _ := Lst.cons _ 5 (Lst.nil _)
#check Lst.append _ as bs -/

-- παλι ταλαιπωρια

-- γιαυτο βαζουμε {...} :
universe v
def Lst (α : Type v) : Type v := List α

def Lst.cons {α : Type v} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type v} : Lst α := List.nil
def Lst.append {α : Type v} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil
def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs

-- το ιδιο μπορω να κανω και στα functions
universe t
def ident {α : Type t} (x : α) := x
-- για τσεκ βαλε παρενθεση, αλλιως θα το βγαλει ολοκληρο
#check (ident)
#check ident 1
#check ident "hello"
#check @ident

-- επισης με τις μεταβλητες:
universe u2

section
  variable {α : Type u1}
  variable (x : α)
  def ident2 := x
end

#check (ident2)
#check ident2
#check ident2 4
#check ident2 "hello"
-- καλη ικανοτητα προβλεψης

-- παντα μπορω να γραψω συγκεκριμενα (e : T) δηλ. το e εχει τυπο Τ
-- σχετικα με αριθμους, αν δεν μπορει να προβλεψει υποθετει Nat
#check 2
#check (2 : Nat)
#check (2 : Int)

-- αν πιο πριν αφησα καποιο ορισμα συναρτησης να εννοειθει (implicit)
-- αλλα τωρα το θελω συγκεκριμενο, κανω πχ την foo , @foo

#check @id
#check @id Nat
#check @id Bool

#check @id Nat 1
#check @id Bool true

end sidequest

end Kef29
