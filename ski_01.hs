{-# LANGUAGE TypeOperators, MultiParamTypeClasses #-}

infixr 7 :->:

data (:->:) a b

class SKI where
  s :: (a :->: (b :->: c)) :->: ((a :->: b) :->: (a :->: c))
  k :: a :->: (b :->: a)
  i :: a :->: a
  mp :: (a :->: b) -> a -> b

b :: SKI => (b :->: c) :->: (a :->: b) :->: a :->: c
b = mp (mp s (mp k s)) k

--y :: SKI => (a :->: a) :->: a
--y = 

--syl :: SKI => (a :->: b) :->: (b :->: c) :->: (a :->: c)
--syl = 

main :: IO ()
main = return ()