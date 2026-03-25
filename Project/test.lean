def A : Type := Nat → Nat

#check A

def g : A :=
  fun x => x + 1

#check g 5
#eval g 5

#check Nat
#check Prop
#check 1
#check True
#check List


variable (x y : Nat)
def f : Nat → Nat → Nat :=
  fun x =>
    fun y =>
      x^2 + y

#check f
#eval f 5
