module PInteger.MultiplicationProofs

import PInteger
import PInteger.AdditionProofs
import Data.Nat

%default total

intMultLeftZero : (a : PInteger) -> 0 * a = 0
intMultLeftZero (Pos k) = Refl
intMultLeftZero (NegS k) = Refl

distributeNegLeft : (a,b : PInteger) -> -a * b = -(a * b)
distributeNegLeft (Pos 0) (Pos b) = Refl
distributeNegLeft (Pos (S k)) (Pos b) = Refl
distributeNegLeft (Pos 0) (NegS b) = Refl
distributeNegLeft (Pos (S k)) (NegS b) = Refl
distributeNegLeft (NegS a) (Pos 0) = rewrite multZeroRightZero a in Refl
distributeNegLeft (NegS a) (Pos (S k)) = Refl
distributeNegLeft (NegS a) (NegS b) = Refl

swapSigns : (a,b : PInteger) -> -a * b = a * -b
swapSigns (Pos 0) (Pos b) = rewrite intMultLeftZero (-(Pos b)) in Refl
swapSigns (Pos (S k)) (Pos 0) = rewrite multZeroRightZero k in Refl
swapSigns (Pos (S k)) (Pos (S j)) = Refl
swapSigns (Pos 0) (NegS b) = Refl
swapSigns (Pos (S k)) (NegS b) = Refl
swapSigns (NegS a) (Pos 0) = rewrite multZeroRightZero a in Refl
swapSigns (NegS a) (Pos (S k)) = Refl
swapSigns (NegS a) (NegS b) = Refl

distributeNegRight : (a,b : PInteger) -> a * -b = -(a * b)
distributeNegRight a b = rewrite sym $ swapSigns a b in distributeNegLeft a b

intMultCommutative : (a,b : PInteger) -> a * b = b * a
intMultCommutative (Pos a) (Pos b) = rewrite multCommutative a b in Refl
intMultCommutative (NegS a) (NegS b) = rewrite multCommutative (S a) (S b) in Refl
intMultCommutative (NegS a) (Pos b) = 
  rewrite multRightSuccPlus b a in
  rewrite multCommutative a b in
  Refl
intMultCommutative (Pos a) (NegS b) = 
  rewrite multRightSuccPlus a b in
  rewrite multCommutative a b in
  Refl

doubleNeg : (a : PInteger) -> -(-a) = a
doubleNeg (Pos k) = case k of { 0 => Refl ; S k => Refl }
doubleNeg (NegS k) = Refl

intMultAssociative : (a,b,c : PInteger) -> a * (b * c) = (a * b) * c
intMultAssociative (Pos a) (Pos b) (Pos c) = 
  rewrite multAssociative a b c in 
  Refl
intMultAssociative (Pos a) (Pos b) (NegS c) = 
  rewrite distributeNegRight (Pos a) (Pos (b * S c)) in
  rewrite multAssociative a b (S c) in
  Refl
intMultAssociative (Pos a) (NegS b) (Pos c) = 
  rewrite distributeNegRight (Pos a) (Pos (S b * c)) in
  rewrite distributeNegLeft (Pos (a * S b)) (Pos c) in
  rewrite multAssociative a (S b) c in
  Refl
intMultAssociative (Pos a) (NegS b) (NegS c) = 
  rewrite distributeNegLeft (Pos (a * S b)) (NegS c) in
  rewrite multAssociative a (S b) (S c) in
  rewrite doubleNeg (Pos ((a * S b) * S c)) in
  Refl
intMultAssociative (NegS a) (Pos b) (Pos c) = 
  rewrite distributeNegLeft (Pos (S a * b)) (Pos c) in 
  rewrite multAssociative (S a) b c in
  Refl
intMultAssociative (NegS a) (Pos b) (NegS c) = 
  rewrite distributeNegLeft (Pos (S a * b)) (NegS c) in
  rewrite distributeNegRight (NegS a) (Pos (b * S c)) in
  rewrite multAssociative (S a) b (S c) in
  Refl
intMultAssociative (NegS a) (NegS b) (Pos c) = 
  rewrite distributeNegRight (NegS a) (Pos (S b * c)) in
  rewrite doubleNeg (Pos (S a * (S b * c))) in
  rewrite multAssociative (S a) (S b) c in
  Refl
intMultAssociative (NegS a) (NegS b) (NegS c) = 
  rewrite multAssociative (S a) (S b) (S c) in 
  Refl

intMultLeftNeutral : (a : PInteger) -> 1 * a = a
intMultLeftNeutral (Pos k) = rewrite plusZeroRightNeutral k in Refl
intMultLeftNeutral (NegS k) = rewrite plusZeroRightNeutral k in Refl

intMultLeftNegate : (a : PInteger) -> -1 * a = -a
intMultLeftNegate (Pos k) = rewrite plusZeroRightNeutral k in Refl
intMultLeftNegate (NegS k) = rewrite plusZeroRightNeutral k in Refl
