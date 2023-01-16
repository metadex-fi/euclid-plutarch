
module Dex.Validator where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)

import Dex.Types
import Dex.Pool
-- import Dex.StateMachine

-- TODO make sure we don't have to check ScriptPurpose, or do check it if required

-- TODO optimize case expressions (probably very inefficient right now)
-- pMkDexValidator :: RegistryNFT -> TokenMetaNFT -> LiquidityNFT -> ClosedTerm PValidator
-- pMkDexValidator registryNFT tokenMetaNFT liquidityNFT = phoistAcyclic $ plam $ \datum redeemer context -> P.do 
--     stateMachineDatum <- pmatch datum
--     case stateMachineDatum of
--         PRegistryDatum  poolsRecord     -> P.do
--             actionRedeemer <- pmatch redeemer 
--             case actionRedeemer of 
--                 PCreateRedeemer createRecord    -> pregisterPool # 
--                 PCloseRedemer   closeRecord     -> punregisterPool
--                 _                               -> perror
--         PTokenMetaDatum tokenMetaRecord -> P.do
--             actionRedeemer <- pmatch redeemer 
--             case actionRedeemer of 
--                 PCreateRedeemer createRecord    -> perror 
--                 PCloseRedemer   closeRecord     -> perror
--                 PSwapRedemer    swapRecord      -> perror
--                 PAddRedemer     addRecord       -> perror
--                 PRemoveRedemer  removeRecord    -> perror
--                 _                               -> perror
--         PLiquidityDatum liquidityrecord -> P.do
--             actionRedeemer <- pmatch redeemer 
--             case actionRedeemer of 
--                 PCreateRedeemer createRecord    -> perror 
--                 PCloseRedemer   closeRecord     -> perror
--                 PSwapRedemer    swapRecord      -> perror
--                 PAddRedemer     addRecord       -> perror
--                 PRemoveRedemer  removeRecord    -> perror
--                 _                               -> perror
--         _                               -> perror
    


{-
Create Pool
    - choose set of tokens; for each
        - choose weight
        - initial n (later: add a rule to optimize this)
        - add initial liquidity >= n for each token
    - determine if pool for those tokens exists with pool registry
    - create for each token:
        - metadata-utxo; carrying (Singular for now)
            - token weight
            - pool id
            - n for that token
            - emitted LP-tokens for that token in that pool
        - n liquidity-utxos; each carrying
            - nonzero amount of the token
            - pool id
-}

createPool :: (Term s PData) -> (Term s PData) -> (Term s PScriptContext) -> (Term s PBool)
createPool dat red ctx = pconstant True

{-
Close Pool
    - return all emitted LP-tokens for all tokens in the pool
    - destroy all utxos
    - return funds
    - remove from pool registry
-}

closePool :: (Term s PData) -> (Term s PData) -> (Term s PScriptContext) -> (Term s PBool)
closePool dat red ctx = pconstant True

{-
Swap
    - choose 
        - pool to trade with
        - pair of tokens; for each
            - delta
            - liquidity-utxo(s) to trade with
                - for now: 
                    - same number in/out
                    - ins/outs needs to end up balanced afterwards 
                - later: require optimal/minimal number of them; i.e.
                    - if a single liquidity-utxo exceeding trade size exists, have to use the smallest of those
                        - otherwise...
                    - have to include a very small one if such exists, for rebalancing
                    - self-balancing utxo-tree
                    - ...
    - read for each token in the pair
        - weight utxo of the pool
        - all liquidity-utxos of the pool
    - check 
        - if reads above are correct 
        - if tokens fit the liquidity-utxos
        - if liquidity-utxos fit each other (same pool id)
        - if remaining liquidity in liquidity-utxo remains nonzero
        - if value equation holds
-}

swap :: (Term s PData) -> (Term s PData) -> (Term s PScriptContext) -> (Term s PBool)
swap dat red ctx = pconstant True

{-
Add Liquidity
    - choose
        - pool
        - set of tokens; for each
            - amount
    - read for each added token
        - all liquidity-utxos in that pool
    - update for each added token
        - metadata-utxo; update
            - weight
                - in proportion to added liquidity, but normalized. i.e. if A*=2 and B*=3 then a*=1 and b*= 1.5
                - later: optimizations needed
            - emitted liquidity-tokens (in proportion to added liquidity)
            - n in proportion to added liquidity
    - create new liquidity-utxos for each added token
        - with nonzero liquidity (later: with optimally split liquidity)
        - with marker-nft
    - send newly emitted LP-tokens to LP
-}

addLiquidity :: (Term s PData) -> (Term s PData) -> (Term s PScriptContext) -> (Term s PBool)
addLiquidity dat red ctx = pconstant True

{-
Remove Liquidity
    - reverse of adding
    - additionally
        - prevent reduction of any token balance to zero
        - question of how to reduce n:
            - which liquidity-utxos to pick? (for now: only constraint is to cover removed liquidity)
            - what to do with the excess? (for now: just put it into another unconstrained liquidity-utxo)
-}

removeLiquidity :: (Term s PData) -> (Term s PData) -> (Term s PScriptContext) -> (Term s PBool)
removeLiquidity dat red ctx = pconstant True