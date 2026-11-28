import Definitions.Def_StreamBucketBank

theorem solution :
    let M := StreamBucketBank.machine 1024 513 16
    M.states = 2273 ∧ M.time = 5435863 ∧ M.descLen = 10310328 ∧ M.cost = 15746191 := by
  decide
