
## Examples

```
/*
 * A simple crowd-funding example
 */
contract FundMe =

  record spend_args = { recipient : address,
                        amount    : int }

  record state = { contributions : map(address, int),
                   total         : int,
                   beneficiary   : address,
                   deadline      : int,
                   goal          : int }

  stateful function spend(args : spend_args) =
    Chain.spend(args.recipient, args.amount)

  entrypoint init(beneficiary, deadline, goal) : state =
    { contributions = {},
      beneficiary   = beneficiary,
      deadline      = deadline,
      total         = 0,
      goal          = goal }

  function is_contributor(addr) =
    Map.member(addr, state.contributions)

  stateful entrypoint contribute() =
    if(Chain.block_height >= state.deadline)
      spend({ recipient = Call.caller, amount = Call.value }) // Refund money
      false
    else
      let amount =
        switch(Map.lookup(Call.caller, state.contributions))
          None    => Call.value
          Some(n) => n + Call.value
      put(state{ contributions[Call.caller] = amount,
                 total @ tot = tot + Call.value })
      true

  stateful entrypoint withdraw() =
    if(Chain.block_height < state.deadline)
      abort("Cannot withdraw before deadline")
    if(Call.caller == state.beneficiary)
      withdraw_beneficiary()
    elif(is_contributor(Call.caller))
      withdraw_contributor()
    else
      abort("Not a contributor or beneficiary")

  stateful function withdraw_beneficiary() =
    require(state.total >= state.goal, "Project was not funded")
    spend({recipient = state.beneficiary,
           amount    = Contract.balance })

  stateful function withdraw_contributor() =
    if(state.total >= state.goal)
      abort("Project was funded")
    let to = Call.caller
    spend({recipient = to,
           amount    = state.contributions[to]})
    put(state{ contributions @ c = Map.delete(to, c) })
```

### Delegation signature

Some chain operations (`Oracle.<operation>` and `AENS.<operation>`) have an
optional delegation signature. This is typically used when a user/accounts
would like to allow a contract to act on it's behalf. The exact data to be
signed varies for the different operations, but in all cases you should prepend
the signature data with the `network_id` (`ae_mainnet` for the Aeternity mainnet, etc.).
