module PInteger

import Data.Nat

%default total

public export 
data PInteger : Type where
  Pos : Nat -> PInteger
  NegS : Nat -> PInteger

export 
toNat : PInteger -> Nat
toNat (Pos n) = n
toNat (NegS n) = S n

export 
Show PInteger where
  show (Pos n) = show n
  show (NegS n) = "-" ++ show (S n)

neg : PInteger -> PInteger
neg (Pos Z) = Pos Z
neg (Pos (S k)) = NegS k
neg (NegS k) = Pos (S k)

export 
Num PInteger where
  fromInteger x = case compareInteger x 0 of 
                       GT => Pos (fromInteger x)
                       EQ => Pos 0
                       LT => NegS (fromInteger ((-x) - 1))
  
  (Pos a) + (Pos b) = Pos (a + b)

  (Pos (S a)) + (NegS (S b)) = assert_smaller (Pos (S a)) (Pos a) + NegS b

  (Pos (S a)) + (-1) = Pos a
  (-1) + (Pos (S b)) = Pos b
  0 + b = b
  a + 0 = a

  (NegS (S a)) + (Pos (S b)) = assert_smaller (NegS (S a)) (NegS a) + Pos b
  (NegS a) + (NegS b) = NegS (S (a + b))

  (Pos a)   * (Pos b)   = Pos (a * b)
  (Pos a)   * (NegS b)  = neg (Pos (a * S b))
  (NegS a)  * (Pos b)   = neg (Pos (S a * b))
  (NegS a)  * (NegS b)  = Pos (S a * S b)

export 
Neg PInteger where
  negate = neg
  x - y = x + negate y

export 
Abs PInteger where
  abs (NegS x) = Pos (S x)
  abs x = x
