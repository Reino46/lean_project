def A : Type := Nat → Nat

#check A 5

def f : A :=
  fun x => x + 1

#check f 5
