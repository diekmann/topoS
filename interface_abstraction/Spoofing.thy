theory Spoofing
imports Network
begin

section{*Can hosts spoof?*}
  definition host_cannot_spoof :: "'v network \<Rightarrow> 'v interface \<Rightarrow> bool" where
    "host_cannot_spoof N start \<equiv> \<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"


  (*if spoofed adresses exist ...*)
  lemma "\<exists> spoofed. spoofed \<noteq> entity start \<Longrightarrow> host_cannot_spoof N start \<Longrightarrow> succ N start = networkboxes (succ N start)"
    apply(rule succ_subset_networkboxes)
    apply(simp add: host_cannot_spoof_def)
    apply(erule exE)
    using succ_subseteq_reachable by fast

  (*if the adress space is so small that there is only one adress, a host cannot spoof (obviously)*)
  lemma "\<not> (\<exists> spoofed. spoofed \<noteq> entity start) \<Longrightarrow> host_cannot_spoof N start"
    by(simp add: host_cannot_spoof_def)
    

  text{*if all networkboxes connected to start block spoofing, start cannot spoof*}
  lemma 
    assumes connected_to_networkboxes: "succ N start = networkboxes (succ N start)" 
      and   no_fwd_spoofed: "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {})"
    shows "host_cannot_spoof N start"
    proof -
      {
      have "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {}) \<Longrightarrow>
                host_cannot_spoof N start"
      apply(simp add: host_cannot_spoof_def)
      apply(clarify)
      apply(erule reachable_induct)
      apply(simp)
      using connected_to_networkboxes apply fast
      apply(simp add: traverse_def)
      using connected_to_networkboxes apply blast
      done
      }
      from this no_fwd_spoofed show ?thesis by simp
    qed


(*
  lemma assumes wf_N: "wellformed_network N"
    shows "host_cannot_spoof N start \<Longrightarrow> \<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {})"
    apply(simp add: host_cannot_spoof_def reachable_eq_rtrancl_view2[OF wf_N] view_def)
    apply(clarsimp)
    apply(erule allE)
    apply(auto)
    (*does not hold?  reachable start \<subseteq> succ start \<Longrightarrow> no forwarding to connected ports*)
    oops
*)


end
