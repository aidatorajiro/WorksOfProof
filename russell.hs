newtype Set x = Set (Either (Set x) x -> Bool)

elements :: Set x -> Either (Set x) x -> Bool
elements (Set f) = f

russell :: Set x
russell = Set (\e -> either (\x -> not $ x `elements` (Left x)) (const False) e)

main :: IO ()
main = print $ russell `elements` (Left russell)
