module Visitors

let visit_block (env : Env.env) fe fs sl =
    if env.is_top then
        let env' = List.fold fe env sl
        List.map (fs { env' with is_top = false }) sl
    else
        let roll =
            (fun (e, l) s ->
            let e' = fe e s in (e', l @ [ fs e' s ]))
        snd (List.fold roll (env, []) sl)
