{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- [公理]
-- 矛盾を許容しないNot
class NCNot n where
    cton :: (forall q. p -> q) -> n p
    ntoc :: n p -> (forall q. p -> q)

-- 排中律
class Classic where
    classic :: NCNot n => Either p (n p)

-- [証明]
-- 三段論法
syllogism :: (p -> q) -> (q -> r) -> (p -> r)
syllogism h1 h2 = h2 . h1

-- 交換法則（かつ）
commutativeLawAnd :: (p, q) -> (q, p)
commutativeLawAnd (p, q) = (q, p)

-- 交換法則（または）
commutativeLawOr :: Either p q -> Either q p
commutativeLawOr (Left  p) = Right p
commutativeLawOr (Right q) = Left  q

-- 結合法則
associativeLaw :: ((p -> q) -> r) -> (p -> (q -> r))
associativeLaw h = const $ h . const

-- P -> Pでない -> Q
bomb :: NCNot n => p -> n p -> q
bomb p np = (ntoc np) p

-- (Pかつ(Pでない))ならばQ
bombAnd :: NCNot n => (p, n p) -> q
bombAnd (p, np) = bomb p np

-- ド・モルガンの法則
deMorgan :: NCNot n => (n p, n q) -> n (Either p q)
deMorgan (np, nq) = cton (\pq ->
    case pq of
        Left  p -> bomb p np
        Right q -> bomb q nq )

-- 二重否定法則
pnnp :: NCNot n => p -> n (n p)
pnnp p = cton $ bomb p

nnpp :: (NCNot n, Classic) => n (n p) -> p
nnpp nnp = case classic of
    Left  p  -> p
    Right np -> bomb np nnp

-- 対偶
contraposition1 :: NCNot n => (p -> q) -> (n q -> n p)
contraposition1 h nq = cton (\p -> bomb (h p) nq)

contraposition2 :: (NCNot n, Classic) => (n q -> n p) -> (p -> q)
contraposition2 h p = nnpp $ (contraposition1 h) (pnnp p)

--いろいろ
imply_to_or :: (NCNot n, Classic) => (p -> q) -> Either (n p) q
imply_to_or pq = case classic of
    Left  r  -> Right $ pq r
    Right nr -> Left nr

-- パースの法則
peirce :: (NCNot n, Classic) => ((p -> q) -> p) -> p
peirce h = case classic of
    Left  p  -> p
    Right np -> case classic of
        Left  q  -> h (\p -> q)
        Right nq -> undefined

-- なんか
prop1 :: (forall p. ((p -> q) -> q)) -> ((p -> q) -> p) -> p
prop1 h h0 = h0 $ const $ h id

main :: IO ()
main = return ()