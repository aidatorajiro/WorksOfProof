{-# LANGUAGE TypeOperators, MultiParamTypeClasses #-}

import Unsafe.Coerce

infixl 7 #

class SKI x where
  s :: x (x a (x b c)) (x (x a b) (x a c))
  k :: x a (x b a)
  i :: x a a
  (#) :: (x a b) -> a -> b -- modus ponens

c :: SKI x => x (x a (x b c)) (x b (x a c))
c = s#(b#b#s)#(k#k)

b :: SKI x => x (x b c) (x (x a b) (x a c))
b = s#(k#s)#k

--m :: SKI (:->:) => (a :->: b) :->: b
--m = s#i#(unsafeCoerce i)

--l :: SKI (:->:) => (a :->: b) :->: (c :->: a) :->: b
--l = c#b#m

--y :: SKI (:->:) => (a :->: a) :->: a
--y = s#l#l

--y :: SKI => (a :->: a) :->: a
--y = s # (k # (s # i # i)) # (s # (s # (k # s) # k) # (k # (s # i # i)))

--syl :: SKI => (a :->: b) :->: (b :->: c) :->: (a :->: c)
--syl = 

main :: IO ()
main = return ()