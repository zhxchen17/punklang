let visit_block env fe fs sl =
  if env.Env.is_top then
    let env' = List.fold_left fe env sl in
    List.map (fs { env' with is_top = false }) sl
  else
    snd (List.fold_left (fun (e, l) s -> let e' = fe e s in
                          (e', l @ [fs e' s])) (env, []) sl)
