{-# LANGUAGE MultiParamTypeClasses #-}

class Unsafe where
    unsafeCoerce :: a -> b

str_to_int :: Unsafe => String -> Int
str_to_int s = unsafeCoerce s

int_to_str :: Unsafe => Int -> String
int_to_str s = unsafeCoerce s

main :: IO ()
main = print "Hello worlds"