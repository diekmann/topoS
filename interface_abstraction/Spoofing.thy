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

 lemma assumes wf_N: "wellformed_network N"
  shows "host_cannot_spoof_ingress N start \<longleftrightarrow> (\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start))"
  (is "?L \<longleftrightarrow> ?R")
  proof
    assume nospoof: "?L"
    { fix spoofed dst
      assume spoofed: "spoofed \<noteq> entity start"
      from nospoof spoofed have "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"
        by(simp add: host_cannot_spoof_ingress_def)
      hence "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> succ N start" using subset_trans networkboxes_subset by metis
      from this reachable_subset_start_iff[OF wf_N] have "\<And>dst. \<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start" by simp
    }
    thus "?R" by simp
    next
    assume notraverese: "?R"
    { fix spoofed dst
      assume spoofed: "spoofed \<noteq> entity start"
      from notraverese spoofed have "\<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start"
        by(simp add: host_cannot_spoof_ingress_def)
      from this reachable_subset_start_iff[OF wf_N, symmetric] have "reachable N (spoofed, dst) start \<subseteq> succ N start" by simp
    }
    (*networkboxes*)
    thus "?L"
      apply(simp add: host_cannot_spoof_ingress_def) 
oops

  lemma assumes wf_N: "wellformed_network N"
    and nospoof: "host_cannot_spoof_ingress N start"
    and spoofed: "spoofed \<noteq> entity start"
    shows "\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {}"
    proof -
      from nospoof spoofed have "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"
        by(simp add: host_cannot_spoof_ingress_def)
      hence "\<forall>dst. reachable N (spoofed, dst) start \<subseteq> succ N start" using subset_trans networkboxes_subset by metis
      from this reachable_subset_start_iff[OF wf_N] have "\<And>dst. \<forall>first_hop\<in>succ N start. traverse N (spoofed, dst) first_hop \<subseteq> succ N start" by simp
      from this traverse_def have "\<And>dst p first_hop. first_hop\<in>succ N start \<Longrightarrow> p\<in>forward N (spoofed, dst) first_hop \<Longrightarrow> 
        succ N \<lparr>entity = entity first_hop, port = p\<rparr> \<subseteq> succ N start" by blast

    show ?thesis
    apply(clarsimp)
    apply(erule allE)
    apply(auto)
    (*does not hold?  reachable start \<subseteq> succ start \<Longrightarrow> no forwarding to connected ports*)
    oops



end
