# MetaDEX v1: Euclid

## New design approach

- emulate AMM-pools as collection of 100% concentrated liquidity pools (I like to term them dirac-pools, but did not come up with the base concept). They can also be seen as order-book limit orders which instead of returning the deposit to the market-maker creates a symmetrical limit order in the other direction, with inverted price.
- what's new (afaik) is the idea to have portfolio-dirac-pools. How this works is that instead of two assets and one spot price it has a map of assets to spot prices (vs. the first of the keyset)
- the previous two points combined result in an n-1 dimensional tensor, where n is the number of assets in the pool. Each entry corresponds to one dirac-pool with a certain combination of spot prices for the assets, denominated in the first asset.
- as we would get a combinatorial explosion of number of dirac-positions ((tick size * tick number) ^ number assets - 1) I afaik came up with the concept of jumping diracs - re-using the same state machine utxo as multiple diracs; imagine it as a sliding window type of thing. Example: If we have 3 active dirac-machines at prices 3, 4, 5, then we can shift the one at 3 to instead serve as 6, the one at 4 to service 7, and so on. Of course this requires accounting for things like "active asset" and "active amounts" instead of just using the value in the utxo.
- note: instead of jumping we could also do smth like "splitting" - jumping but leaving the old one around. This would split up the costs of the combinatorial explosion; each trader will just experience a bit of additional fixed fees in effect. Will have to see if this has any advantages. postponed for now, implementing jumping first.


## Implementation notes

machines/utxos/datums:

- reference: stores constant stuff
    - datum:
        - pool owner
        - asset -> jump size (first asset not needed)
        - default liquidity & active asset generator: p2,...,pN -> (amnt A1, active asset)

    - value:
        - some NFT to ID it to diracs - tokenname = hash of owneraddress (for now)

    - actions:
        - create: ensure
            - NFT/owner fits creating address
            - datum is correctly formatted (to avoid cranking the users in the frontend)
        - edit: ensure
            - owner edits
            - datum is correctly formatted (to avoid cranking the users in the frontend)
        - close: ensure
            - owner closes
            - all diracs closed (to avoid cranking the users in the frontend) - TODO needs some design work

- dirac: stores variable stuff (for now)
    - datum:
        - reference ID NFT
        - asset -> price in A1
        - asset -> active amnt
        - pre-jump active asset storage: (p2,...,pN) -> asset or p2 -> ... -> pN -> asset

    - actions:
        - open:
            - no checks for now 
            - later: work with NFTs to ensure everything is correct, to avoid cranking the users in the frontend
        - close
            - check the owner
            - later: probably want to count active diracs in reference, update this correctly
        - flip
            - value-delta equals active-amounts-delta
            - no negative active amounts
            - deltas and prices align
            - rest of datum stays the same
        - jump: check that
            - there is only one active asset pre-jump
            - if it's different from default: it's added to storage
            - jump size is correct
            - if jump target is in storage
                - if it is: it's loaded correctly, and removed from storage
                - if it isn't: default generated correctly
            - active amounts pre-flip are generated correctly
            - minimum amount is flipped
            - check flip