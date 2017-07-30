{-# LANGUAGE TypeOperators, MultiParamTypeClasses #-}

import Unsafe.Coerce

infixr 7 :->:
infixl 7 #

data (:->:) a b

class SKI where
  s :: (a :->: b :->: c) :->: (a :->: b) :->: a :->: c
  k :: a :->: b :->: a
  i :: a :->: a
  (#) :: (a :->: b) -> a -> b -- modus ponens

newtype I a = I (I a :->: a)

unI :: I a -> I a :->: a
unI (I x) = x
{-# NOINLINE unI #-}

c :: SKI => (a :->: b :->: c) :->: b :->: a :->: c
c = s#(b#b#s)#(k#k)

b :: SKI => (b :->: c) :->: (a :->: b) :->: a :->: c
b = s#(k#s)#k

m :: SKI => I a :->: a
m = (s unI)#i

l :: SKI => (a :->: b) :->: I a :->: b
l = c#b#m

y :: SKI => (a :->: a) :->: a
y = s#l#(b#I#l)

--y :: SKI => (a :->: a) :->: a
--y = s # (k # (s # i # i)) # (s # (s # (k # s) # k) # (k # (s # i # i)))

--syl :: SKI => (a :->: b) :->: (b :->: c) :->: (a :->: c)
--syl = 

main :: IO ()
main = return ()