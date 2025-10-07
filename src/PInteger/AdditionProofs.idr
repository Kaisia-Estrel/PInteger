module PInteger.AdditionProofs

import PInteger
import Data.Nat

%default total

export
left_PosIdentity : (a : PInteger) -> Pos Z + a = a
left_PosIdentity (Pos 0) = Refl
left_PosIdentity (Pos (S k)) = Refl
left_PosIdentity (Neg 0) = pos0_neg0_equality
left_PosIdentity (Neg (S k)) = Refl

export
left_NegIdentity : (a : PInteger) -> Neg Z + a = a
left_NegIdentity a =  
    rewrite sym pos0_neg0_equality in
      left_PosIdentity a

export
combinePos : (a,b : Nat) -> Pos a + Pos b = Pos (a + b)
combinePos a 0 = rewrite plusZeroRightNeutral a in Refl
combinePos 0 b = left_PosIdentity (Pos b)
combinePos (S j) (S k) = Refl


export
combineNeg : (a,b : Nat) -> Neg a + Neg b = Neg (a + b)
combineNeg a 0 = rewrite plusZeroRightNeutral a in Refl
combineNeg 0 b = rewrite sym pos0_neg0_equality in 
                 rewrite left_PosIdentity (Neg b) in 
                          Refl
combineNeg (S a) (S b) = Refl

export
plus_pos_s_eq : (a,b : Nat) -> Pos (S a) = Pos (S b) -> Pos a = Pos b
plus_pos_s_eq 0 0 Refl = Refl
plus_pos_s_eq (S k) (S k) Refl = Refl

export
plusAssoc : (a,b,c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc 0 b c = Refl
plusAssoc (S k) b c = rewrite plusAssoc k b c in Refl

export
inverse_identity : (a : Nat) -> Pos a + Neg a = Pos Z
inverse_identity 0 = Refl
inverse_identity (S k) = inverse_identity k

export
intPlusCommutative : (a,b : PInteger) -> a + b = b + a
intPlusCommutative (Pos 0) b = rewrite left_PosIdentity b in Refl
intPlusCommutative (Neg 0) b = 
  rewrite sym pos0_neg0_equality in 
  rewrite left_PosIdentity b in 
          Refl
intPlusCommutative (Pos (S k)) (Pos j) = 
  rewrite combinePos (S k) j in
  rewrite combinePos j (S k) in
  rewrite sym $ plusSuccRightSucc j k in
  rewrite plusCommutative j k in
    Refl
intPlusCommutative (Pos (S k)) (Neg 0) = Refl
intPlusCommutative (Neg (S k)) (Neg j) = 
  rewrite combineNeg (S k) j in
  rewrite combineNeg j (S k) in
  rewrite sym $ plusSuccRightSucc j k in
  rewrite plusCommutative j k in
    Refl
intPlusCommutative (Neg (S k)) (Pos 0) = Refl
intPlusCommutative (Pos (S n)) (Neg (S m)) = 
  rewrite intPlusCommutative (Pos n) (assert_smaller (Neg (S m)) $ Neg m) in
    Refl
intPlusCommutative (Neg (S n)) (Pos (S m)) = 
  rewrite intPlusCommutative (Neg n) (assert_smaller (Pos (S m)) $ Pos m) in
    Refl

export
both_s_equal : (a,b : Nat) -> (c : PInteger) 
            -> c + Pos (S a) = Pos (S b) + c 
            -> c + Pos a = Pos b + c 
both_s_equal a b (Pos c) eq = 
    rewrite combinePos b c in
    rewrite plusCommutative b c in
    rewrite sym $ combinePos c b in
    rewrite combinePos c a in 
    rewrite combinePos c b in 
    rewrite plusCommutative c b in 
      plus_pos_s_eq (c + a) (b + c) $
    rewrite plusSuccRightSucc c a in sym 
    $ trans (sym (combinePos (S b) c))
    $ sym
    $ trans (sym (combinePos c (S a))) eq

export
intPlusAssociative : (a, b, c : PInteger) -> (a + b) + c = a + (b + c)
intPlusAssociative (Pos i) (Pos j) (Pos k) = 
  rewrite combinePos i j in 
  rewrite combinePos j k in 
  rewrite combinePos (i+j) k in 
  rewrite combinePos i (j+k) in 
  rewrite plusAssoc i j k in
    Refl

intPlusAssociative (Pos a) (Pos b) (Neg 0) = Refl
intPlusAssociative (Pos a) (Pos 0) (Neg (S k)) = Refl
intPlusAssociative (Pos a) (Pos (S b)) (Neg (S c)) = 
  rewrite combinePos a (S b) in
  rewrite sym $ plusSuccRightSucc a b in
  rewrite sym $ combinePos a b in
  rewrite intPlusAssociative (Pos a) (assert_smaller (Pos (S b)) $ Pos b) (Neg c) in
    Refl

intPlusAssociative (Pos k) (Neg j) (Pos 0) = Refl
intPlusAssociative (Pos k) (Neg 0) (Pos (S i)) = Refl
intPlusAssociative (Pos 0) (Neg (S j)) (Pos (S i)) = 
  rewrite left_PosIdentity (Neg j + Pos i) in
  Refl
intPlusAssociative (Pos (S k)) (Neg (S j)) (Pos (S i)) = 
  rewrite intPlusCommutative (Pos $ S k) (Neg $ S j) in
  rewrite intPlusAssociative (assert_smaller (Neg (S j)) $ Neg j) (assert_smaller (Pos (S k)) $ Pos k) (Pos (S i)) in
  rewrite intPlusCommutative (Neg j) (Pos i) in
  rewrite assert_total $ sym $ intPlusAssociative (Pos (S k)) (Pos i) (Neg j) in
  rewrite intPlusCommutative (Pos $ S k) (Pos i) in
  rewrite intPlusCommutative ((Pos i) + (Pos $ S k)) (Neg j) in
  rewrite combinePos k (S i) in 
  rewrite combinePos i (S k) in 
  rewrite sym $ plusSuccRightSucc i k in
  rewrite sym $ plusSuccRightSucc k i in
  rewrite plusCommutative k i in
  Refl

intPlusAssociative (Pos 0) (Neg 0) (Neg c) = 
  rewrite left_NegIdentity (Neg c) in
  rewrite left_PosIdentity (Neg c) in
    Refl
intPlusAssociative (Pos 0) (Neg (S k)) (Neg c) = 
  rewrite left_PosIdentity ((Neg (S k) + Neg c)) in Refl
intPlusAssociative (Pos (S k)) (Neg 0) (Neg c) = 
  rewrite left_NegIdentity (Neg c) in Refl
intPlusAssociative (Pos (S k)) (Neg (S j)) (Neg c) = 
  rewrite combineNeg (S j) c in
  rewrite sym $ combineNeg j c in
  rewrite intPlusAssociative (assert_smaller (Pos (S k)) $ Pos k) (assert_smaller (Neg (S j)) $ Neg j) (Neg c) in
  Refl

intPlusAssociative (Neg 0) (Pos j) (Pos i) = 
  rewrite left_NegIdentity (Pos j) in
  rewrite left_NegIdentity (Pos j + Pos i) in
    Refl
intPlusAssociative (Neg (S k)) (Pos 0) (Pos i) = 
  rewrite left_PosIdentity (Pos i) in Refl
intPlusAssociative (Neg (S k)) (Pos (S j)) (Pos i) = 
  rewrite combinePos (S j) i in
  rewrite sym $ combinePos j i in
  rewrite intPlusAssociative (assert_smaller (Neg (S k)) $ Neg k) (assert_smaller (Pos (S j)) $ Pos j) (Pos i) in
  Refl

intPlusAssociative (Neg 0) (Pos j) (Neg i) = 
  rewrite left_NegIdentity (Pos j) in
  rewrite left_NegIdentity (Pos j + Neg i) in
  Refl
intPlusAssociative (Neg (S k)) (Pos 0) (Neg i) = 
  rewrite left_PosIdentity (Neg i) in Refl
intPlusAssociative (Neg (S k)) (Pos (S j)) (Neg 0) = Refl
intPlusAssociative (Neg (S k)) (Pos (S j)) (Neg (S i)) = 
  rewrite intPlusCommutative (Neg k) (Pos j) in
  rewrite intPlusCommutative (Pos j) (Neg i) in
  rewrite intPlusAssociative (assert_smaller (Pos (S j)) $ Pos j) (assert_smaller (Neg (S k)) $ Neg k) (Neg (S i)) in
  rewrite assert_total $ sym $ intPlusAssociative (Neg (S k)) (assert_smaller (Neg (S i)) $ Neg i) (assert_smaller (Pos (S j)) $ Pos j) in
  rewrite combineNeg k (S i) in
  rewrite combineNeg (S k) i in
  rewrite sym $ plusSuccRightSucc k i in
  rewrite intPlusCommutative (Pos j) (Neg (S (k + i))) in
  Refl

intPlusAssociative (Neg k) (Neg j) (Pos 0) = Refl
intPlusAssociative (Neg k) (Neg 0) (Pos (S i)) = Refl
intPlusAssociative (Neg k) (Neg (S j)) (Pos (S i)) = 
  rewrite combineNeg k (S j) in
  rewrite sym $ plusSuccRightSucc k j in
  rewrite sym $ combineNeg k j in
  rewrite intPlusAssociative ( Neg k) (assert_smaller (Neg (S j)) $ Neg j) (Pos i) in
  Refl

intPlusAssociative (Neg a) (Neg b) (Neg c) = 
  rewrite combineNeg a b in
  rewrite combineNeg (a+b) c in
  rewrite combineNeg b c in
  rewrite combineNeg a (b + c) in
  rewrite plusAssoc a b c in
  Refl

intPlusAssociative (Neg 0) (Neg b) (Pos (S c)) = 
  rewrite left_PosIdentity (Pos (S c)) in
  rewrite left_NegIdentity (Neg b) in
  rewrite left_NegIdentity (Neg b + Pos (S c)) in
  Refl

intPlusAssociative (Neg (S a)) (Neg 0) (Pos c) = 
  rewrite left_NegIdentity (Pos c) in Refl
intPlusAssociative (Neg (S a)) (Neg (S k)) (Pos 0) = Refl
intPlusAssociative (Neg (S a)) (Neg (S k)) (Pos (S j)) = 
  rewrite sym $ plusSuccRightSucc a k in
  rewrite plusCommutative a k in
  rewrite plusSuccRightSucc k a in
  rewrite plusCommutative k (S a) in
  rewrite sym $ combineNeg (S a) k in
  rewrite intPlusAssociative (Neg (S a)) (assert_smaller (Neg (S k)) $ Neg k) (Pos j) in
  Refl
