Require Import ZArith.

Module Nat2Z.

Notation inj_lt := Nat2Z.inj_lt.
Notation inj_le := Nat2Z.inj_le.
Notation inj := Nat2Z.inj.

Lemma inj_div n m : Z.of_nat (n / m) = (Z.of_nat n / Z.of_nat m)%Z.
Proof. now case m; [case n|intro m'; apply div_Zdiv]. Qed.

End Nat2Z.
