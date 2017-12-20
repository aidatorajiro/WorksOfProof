{-# LANGUAGE TypeOperators, MultiParamTypeClasses #-}

infixr 7 :->:
infixl 7 #

data (:->:) a b

class SKI where
  s :: (a :->: b :->: c) :->: (a :->: b) :->: a :->: c
  k :: a :->: b :->: a
  i :: a :->: a
  (#) :: (a :->: b) -> a -> b -- modus ponens

c :: SKI => (a :->: b :->: c) :->: b :->: a :->: c
c = s#(b#b#s)#(k#k)

b :: SKI => (b :->: c) :->: (a :->: b) :->: a :->: c
b = s#(k#s)#k

m :: SKI => (a :->: b) :->: b
m = s#i#i

l :: SKI => (a :->: b) :->: (c :->: a) :->: b
l = c#b#m

y :: SKI => (a :->: a) :->: a
y = s#l#l

--y :: SKI => (a :->: a) :->: a
--y = s # (k # (s # i # i)) # (s # (s # (k # s) # k) # (k # (s # i # i)))

--syl :: SKI => (a :->: b) :->: (b :->: c) :->: (a :->: c)
--syl = 

main :: IO ()
main = return ()