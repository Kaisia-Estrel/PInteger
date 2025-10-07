module PInteger.MultiplicationProofs

import PInteger
import PInteger.AdditionProofs
import Data.Nat

%default total

left_MultZero : (a : PInteger) -> Pos 0 * a = Pos 0
left_MultZero a = Refl

right_MultZero : (a : PInteger) -> a * Pos 0 = Pos 0
right_MultZero (Pos 0) = Refl
right_MultZero (Pos 1) = Refl
right_MultZero (Pos (S (S k))) = Refl
right_MultZero (Neg 0) = Refl
right_MultZero (Neg 1) = rewrite pos0_neg0_equality in Refl
right_MultZero (Neg (S (S k))) = Refl

left_MultPosOne : (a : PInteger) -> Pos 1 * a = a
left_MultPosOne (Pos 0) = Refl
left_MultPosOne (Pos (S k)) = Refl
left_MultPosOne (Neg 0) = rewrite pos0_neg0_equality in Refl
left_MultPosOne (Neg (S k)) = Refl

right_MultPosOne : (a : PInteger) -> a * Pos 1 = a
right_MultPosOne (Pos 0) = Refl
right_MultPosOne (Pos 1) = Refl
right_MultPosOne (Pos (S (S k))) = Refl
right_MultPosOne (Neg 0) = rewrite pos0_neg0_equality in Refl
right_MultPosOne (Neg 1) = Refl
right_MultPosOne (Neg (S (S k))) = Refl

left_MultNegOne : (a : PInteger) -> Neg 1 * a = negate a
left_MultNegOne (Pos 0) = rewrite pos0_neg0_equality in Refl
left_MultNegOne (Pos 1) = Refl
left_MultNegOne (Pos (S (S k))) = Refl
left_MultNegOne (Neg 0) = Refl
left_MultNegOne (Neg (S 0)) = Refl
left_MultNegOne (Neg (S (S k))) = Refl

right_MultNegOne : (a : PInteger) -> a * Neg 1 = negate a
right_MultNegOne (Pos 0) = rewrite pos0_neg0_equality in Refl
right_MultNegOne (Pos 1) = Refl
right_MultNegOne (Pos (S (S k))) = Refl
right_MultNegOne (Neg 0) = Refl
right_MultNegOne (Neg (S 0)) = Refl
right_MultNegOne (Neg (S (S k))) = Refl

mult_plus_s_pos : (a : PInteger) -> (b : Nat) -> a * Pos (S b) = a + (a * Pos b) 
mult_plus_s_pos a 0 = rewrite right_MultZero a in rewrite right_MultPosOne a in Refl
mult_plus_s_pos (Pos 0) 1 = Refl
mult_plus_s_pos (Pos 1) 1 = Refl
mult_plus_s_pos (Pos (S (S k))) 1 = Refl
mult_plus_s_pos (Neg 0) 1 = rewrite pos0_neg0_equality in Refl
mult_plus_s_pos (Neg 1) 1 = Refl
mult_plus_s_pos (Neg (S (S k))) 1 = Refl
mult_plus_s_pos (Pos 0) (S k) = Refl
mult_plus_s_pos (Pos (S 0)) (S k) = Refl
mult_plus_s_pos (Pos (S (S j))) (S k) = Refl
mult_plus_s_pos (Neg 0) (S k) = rewrite pos0_neg0_equality in Refl
mult_plus_s_pos (Neg 1) (S k) = rewrite left_MultNegOne (Pos (S k)) in Refl
mult_plus_s_pos (Neg (S (S j))) (S k) = Refl

same_sign_mult_eq : (a,b : Nat) -> Neg a * Neg b = Pos a * Pos b
same_sign_mult_eq 0 b = Refl
same_sign_mult_eq (S k) 0 = Refl
same_sign_mult_eq 1 (S j) = Refl
same_sign_mult_eq (S (S k)) 1 = Refl
same_sign_mult_eq (S (S k)) (S (S j)) = Refl

mult_plus_s_neg : (a : PInteger) -> (b : Nat) -> a * Neg (S b) = negate a + (a * Neg b) 
mult_plus_s_neg (Pos k) 0 = rewrite right_MultNegOne (Pos k) in 
                            rewrite sym pos0_neg0_equality in 
                            rewrite right_MultZero (Pos k) in Refl
mult_plus_s_neg (Neg k) 0 = 
    rewrite right_MultNegOne (Neg k) in 
    rewrite sym pos0_neg0_equality in 
    rewrite right_MultZero (Neg k) in 
      Refl
mult_plus_s_neg (Pos 0) (S k) = pos0_neg0_equality
mult_plus_s_neg (Pos 1) (S k) = Refl
mult_plus_s_neg (Pos (S (S j))) (S k) = Refl
mult_plus_s_neg (Neg 0) (S k) = Refl
mult_plus_s_neg (Neg 1) (S k) = Refl
mult_plus_s_neg (Neg (S (S j))) (S k) = rewrite same_sign_mult_eq (S (S j)) (S k) in Refl

lift_pos_mult : (a,b : Nat) -> Pos a * Pos b = Pos (a * b)
lift_pos_mult 0 b = Refl
lift_pos_mult (S k) 0 = rewrite multZeroRightZero k in Refl
lift_pos_mult (S 0) (S j) = rewrite plusZeroRightNeutral j in Refl
lift_pos_mult (S (S k)) (S 0) = rewrite multOneRightNeutral k in Refl
lift_pos_mult (S (S a)) (S (S b)) = 
  rewrite lift_pos_mult (S (S a)) (S b)  in 
  rewrite multCommutative a (S b) in
  rewrite multCommutative a (S (S b)) in
  rewrite multCommutative b a in
  rewrite sym $ multRightSuccPlus a b in
  rewrite multCommutative a (S b) in
  rewrite sym $ multRightSuccPlus (S b) a in
  rewrite sym $ multRightSuccPlus (S b) (S a) in
  rewrite multCommutative (S b) (S (S a)) in
  rewrite sym $ multRightSuccPlus (S (S a)) (S b) in
  rewrite multCommutative b a in
  rewrite sym $ multRightSuccPlus a b in
  rewrite sym $ multRightSuccPlus a (S b) in
    Refl

lift_neg_mult : (a,b : Nat) -> Neg a * Neg b = Pos (a * b)
lift_neg_mult a b = 
  rewrite same_sign_mult_eq a b in
  rewrite lift_pos_mult a b in
  Refl

swap_signs : (a,b : Nat) -> Pos a * Neg b = Neg a * Pos b
swap_signs 0 a = Refl
swap_signs a 0 = 
  rewrite sym pos0_neg0_equality in 
  rewrite right_MultZero (Pos a) in 
  rewrite right_MultZero (Neg a) in 
          Refl
swap_signs (S 0) b = 
  rewrite left_MultPosOne (Neg b) in
  rewrite left_MultNegOne (Pos b) in
  Refl
swap_signs (S (S k)) (S 0) = Refl
swap_signs (S (S k)) (S (S j)) = rewrite swap_signs (S (S k)) (S j) in Refl

lift_nat_mult_prf : (a,b : Nat) -> (a * b = c * d) -> Pos a * Pos b = Pos c * Pos d
lift_nat_mult_prf a b {c,d} prf = rewrite lift_pos_mult a b in rewrite prf in rewrite sym $ lift_pos_mult c d in Refl

plus_assoc_commute : (a,b,c : Nat) -> a + (b + c) = b + (a + c)
plus_assoc_commute a b c = 
  rewrite plusAssociative a b c in 
  rewrite plusCommutative a b in
  rewrite sym $ plusAssociative b a c in 
          Refl

distribute_negation : (a,b : Nat) -> Pos a * Neg b = Neg (a * b)
distribute_negation 0 b = rewrite pos0_neg0_equality in Refl
distribute_negation (S k) 0 = rewrite multZeroRightZero k in rewrite pos0_neg0_equality in Refl
distribute_negation 1 (S j) = rewrite plusZeroRightNeutral j in Refl
distribute_negation (S (S k)) 1 = rewrite multOneRightNeutral k in Refl
distribute_negation (S (S k)) (S (S j)) = 
  rewrite distribute_negation (S (S k)) (S j) in  
  rewrite sym $ plusSuccRightSucc j (j + (k * S j)) in
  rewrite sym $ plusSuccRightSucc k (S (j + (j + (k * (S j))))) in
  rewrite sym $ plusSuccRightSucc k (j + (j + (k * (S j)))) in
  rewrite sym $ plusSuccRightSucc j (S (j + (k * S (S j)))) in
  rewrite sym $ plusSuccRightSucc j (j + (k * S (S j))) in
  rewrite multRightSuccPlus k (S j) in
  rewrite multRightSuccPlus k j in
  rewrite plus_assoc_commute j k (k + (k * j)) in
  rewrite plus_assoc_commute j k (j + (k + (k * j))) in
      Refl

int_mult_commutative : (a,b : PInteger) -> a * b = b * a
int_mult_commutative (Pos k) (Pos j) = 
  rewrite lift_nat_mult_prf k j (multCommutative k j) in
    Refl
int_mult_commutative (Neg k) (Neg j) = 
  rewrite same_sign_mult_eq k j in
  rewrite lift_nat_mult_prf k j (multCommutative k j) in
  rewrite same_sign_mult_eq j k in
  Refl
int_mult_commutative (Pos k) (Neg j) = 
  rewrite distribute_negation k j in
  rewrite multCommutative k j in
  rewrite sym $ distribute_negation j k in
  rewrite swap_signs j k in
    Refl
int_mult_commutative (Neg k) (Pos j) = 
  rewrite sym $ swap_signs k j in
  rewrite distribute_negation k j in
  rewrite multCommutative k j in
  rewrite sym $ distribute_negation j k in
  rewrite swap_signs j k in
  Refl

int_mult_associative : (a,b,c : PInteger) -> a * (b * c) = (a * b) * c
int_mult_associative (Pos k) (Pos j) (Pos i) = 
  rewrite lift_pos_mult j i in
  rewrite lift_pos_mult k j in
  rewrite lift_pos_mult k (j * i) in
  rewrite lift_pos_mult (k * j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Pos k) (Pos j) (Neg i) = 
  rewrite distribute_negation j i in
  rewrite lift_pos_mult k j in
  rewrite distribute_negation k (j * i) in
  rewrite distribute_negation (k * j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Pos k) (Neg j) (Pos i) = 
  rewrite distribute_negation k j in
  rewrite sym $ swap_signs j i in
  rewrite distribute_negation j i in
  rewrite distribute_negation k (j * i) in
  rewrite sym $ swap_signs (k * j) i in
  rewrite distribute_negation (k * j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Pos k) (Neg j) (Neg i) = 
  rewrite same_sign_mult_eq j i in
  rewrite distribute_negation k j in
  rewrite lift_pos_mult j i in
  rewrite lift_pos_mult k (j*i) in
  rewrite same_sign_mult_eq (k*j) i in
  rewrite lift_pos_mult (k*j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Neg k) (Pos j) (Pos i) = 
  rewrite lift_pos_mult j i in
  rewrite sym $ swap_signs k (j * i) in
  rewrite distribute_negation k (j * i) in
  rewrite sym $ swap_signs k j in
  rewrite distribute_negation k j in
  rewrite sym $ swap_signs (k * j) i in
  rewrite distribute_negation (k * j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Neg k) (Pos j) (Neg i) = 
  rewrite distribute_negation j i in
  rewrite sym $ swap_signs k j in
  rewrite distribute_negation k j in
  rewrite lift_neg_mult k (j * i) in
  rewrite lift_neg_mult (k * j) i in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Neg k) (Neg j) (Pos i) = 
  rewrite lift_neg_mult k j in
  rewrite lift_pos_mult (k*j) i in
  rewrite sym $ swap_signs j i in
  rewrite distribute_negation j i in
  rewrite lift_neg_mult k (j*i) in
  rewrite multAssociative k j i in
  Refl
int_mult_associative (Neg k) (Neg j) (Neg i) = 
  rewrite lift_neg_mult j i in
  rewrite lift_neg_mult k j in
  rewrite sym $ swap_signs k (j*i) in
  rewrite distribute_negation k (j*i) in
  rewrite distribute_negation (k*j) i in
  rewrite multAssociative k j i in
  Refl
