def A : Type := Nat → Nat

#check A

def f : A :=
  fun x => x + 1

#check f 5
