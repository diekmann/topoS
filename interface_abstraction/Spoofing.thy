theory Spoofing
imports Network_View
begin

section{*Can hosts spoof?*}
  definition host_cannot_spoof_ingress :: "'v network \<Rightarrow> 'v interface \<Rightarrow> bool" where
    "host_cannot_spoof_ingress N start \<equiv> \<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"


  (*if spoofed adresses exist ...*)
  lemma "\<exists> spoofed. spoofed \<noteq> entity start \<Longrightarrow> host_cannot_spoof_ingress N start \<Longrightarrow> succ N start = networkboxes (succ N start)"
    apply(rule succ_subset_networkboxes)
    apply(simp add: host_cannot_spoof_ingress_def)
    apply(erule exE)
    using succ_subseteq_reachable by fast

  (*if the adress space is so small that there is only one adress, a host cannot spoof (obviously)*)
  lemma "\<not> (\<exists> spoofed. spoofed \<noteq> entity start) \<Longrightarrow> host_cannot_spoof_ingress N start"
    by(simp add: host_cannot_spoof_ingress_def)
    
  text{*An alternative definition of host_cannot_spoof_ingress
        * only networkboxes must be reachable
        * traversing the first hop must never get one further into the network (it can loop back to the start) *}
  lemma host_cannot_spoof_ingress_alt:
  assumes wf_N: "wellformed_network N"
  and existsspoof: "\<exists> spoofed. spoofed \<noteq> entity start"
  shows "host_cannot_spoof_ingress N start \<longleftrightarrow> 
    (\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start)) \<and> 
    succ N start = networkboxes (succ N start)"
  (is "?L \<longleftrightarrow> ?R1 \<and> ?R2")
  proof
    assume nospoof: "?L"
    from existsspoof nospoof have connected_to_networkboxes: "succ N start = networkboxes (succ N start)" 
      by (metis (full_types) host_cannot_spoof_ingress_def order_trans succ_subset_networkboxes succ_subseteq_reachable)
    { fix spoofed dst
      assume spoofed: "spoofed \<noteq> entity start"
      from nospoof spoofed have "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"
        by(simp add: host_cannot_spoof_ingress_def)
      hence "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> succ N start" using subset_trans networkboxes_subset by metis
      from this reachable_subset_start_iff[OF wf_N] have "\<And>dst. \<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start" by simp
    }
    hence "?R1" by simp
    from this connected_to_networkboxes show "?R1 \<and> ?R2" ..
    next
    assume "?R1 \<and> ?R2"
    hence notraverese: "?R1" and networkboxes: "?R2" by auto
    { fix spoofed dst
      assume spoofed: "spoofed \<noteq> entity start"
      from notraverese spoofed have "\<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start"
        by(simp add: host_cannot_spoof_ingress_def)
      from this reachable_subset_start_iff[OF wf_N, symmetric] have "reachable N (spoofed, dst) start \<subseteq> succ N start" by simp
      from this networkboxes have "reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)" by simp
    }
    thus "?L"
      by(simp add: host_cannot_spoof_ingress_def) 
  qed
  


  text{*if all networkboxes connected to start block spoofing, start cannot spoof*}
  lemma 
    assumes connected_to_networkboxes: "succ N start = networkboxes (succ N start)" 
      and   no_fwd_spoofed: "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {})"
    shows "host_cannot_spoof_ingress N start"
    proof -
      {
      have "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {}) \<Longrightarrow>
                host_cannot_spoof_ingress N start"
      apply(simp add: host_cannot_spoof_ingress_def)
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



end
