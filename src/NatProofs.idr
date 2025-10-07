module NatProofs

-- A module mostly for practice with proving basic Natural number
-- addition and multiplication axioms.

plus_s_right_s : (a,b : Nat) -> S (a + b) = a + S b
plus_s_right_s 0 b = Refl
plus_s_right_s (S k) b = rewrite plus_s_right_s k b in Refl

plus_s_left_s : (a,b : Nat) -> S (a + b) = S a + b
plus_s_left_s _ _ = Refl

plus_right_identity : (a : Nat) -> a + 0 = a
plus_right_identity 0 = Refl
plus_right_identity (S k) = rewrite plus_right_identity k in Refl

plus_commutes : (a,b : Nat) -> a + b = b + a
plus_commutes 0 b = sym (plus_right_identity b)
plus_commutes (S k) b = 
    rewrite plus_commutes {a = k, b} in 
    rewrite plus_s_right_s b k in 
            sym Refl

plusAssoc : (a,b,c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc 0 b c = Refl
plusAssoc (S k) b c = rewrite plusAssoc k b c in Refl

mult_z_right : (a : Nat) -> a * 0 = 0
mult_z_right 0 = Refl
mult_z_right (S k) = mult_z_right k

nat_plus_z_identity : (a : Nat) -> a + 0 = a
nat_plus_z_identity 0 = Refl
nat_plus_z_identity (S k) = rewrite nat_plus_z_identity k in Refl

nat_mult_1_identity : (a : Nat) -> a * 1 = a
nat_mult_1_identity 0 = Refl
nat_mult_1_identity (S k) = rewrite nat_mult_1_identity k in Refl

mult_plus_s : (a,b : Nat) -> a + (a * b) = a * (S b)
mult_plus_s 0 b = Refl
mult_plus_s (S a) b = 
  rewrite sym $ mult_plus_s a b in
  rewrite plusAssoc b a (a * b) in
  rewrite plus_commutes b a in
  rewrite sym $ plusAssoc a b (a * b) in 
    Refl

nat_mult_commutes : (a,b : Nat) -> a * b = b * a
nat_mult_commutes 0 b = rewrite mult_z_right b in Refl
nat_mult_commutes (S k) b = 
  rewrite nat_mult_commutes k b in
    mult_plus_s b k

nat_mult_distributive : (a,b,c : Nat) -> a * (b + c) = a * b + a * c
nat_mult_distributive 0 b c = Refl
nat_mult_distributive (S a) b c = 
  rewrite nat_mult_distributive a b c in
  rewrite sym (plusAssoc b c ((a*b) + (a*c))) in
  rewrite plus_commutes (a*b) (a*c) in
  rewrite plusAssoc c (a*c) (a*b) in
  rewrite nat_mult_commutes a c in
  rewrite mult_plus_s c a in
  rewrite plus_commutes (c * (S a)) (a*b) in
  rewrite plusAssoc b (a*b) (c * S a) in
  rewrite nat_mult_commutes a b in
  rewrite mult_plus_s b a in
  Refl

nat_mult_assoc : (a,b,c : Nat) -> a * (b * c) = (a * b) * c
nat_mult_assoc 0 b c = Refl
nat_mult_assoc a 0 c = rewrite mult_z_right a in Refl
nat_mult_assoc a b 0 =  
  rewrite mult_z_right b in 
  rewrite mult_z_right (a * b) in 
  rewrite mult_z_right a in 
    Refl
nat_mult_assoc a b (S c) = 
    rewrite sym $ mult_plus_s b c in
    rewrite nat_mult_distributive a b (b * c) in
    rewrite nat_mult_assoc a b c in
    rewrite mult_plus_s (a * b) c in
    Refl
