theory Efficient_Distinct
imports 
"./isabelle_afp/Automatic_Refinement/Lib/Misc" (*mergesort*)
"~~/src/HOL/Library/List_lexord"

(*"~~/src/HOL/Library/Char_nat"*)
(*"~~/src/HOL/Library/Product_ord" conflict with collections *)
(*"isabelle_afp/Efficient-Mergesort/Efficient_Sort" not tail recursive*)

"~~/src/HOL/Library/Code_Char"
(*"~~/src/HOL/Library/Code_Char_chr" 2013-2*)
(*"~~/src/HOL/Library/Code_Char_ord"* 2013-2*)
begin

text {*efficient distinct code*}


  lemma list_length_iff_distinct: 
  "\<lbrakk>set xs = set ys; distinct ys\<rbrakk> \<Longrightarrow> distinct xs \<longleftrightarrow> length xs = length ys"
  proof
    assume "set xs = set ys" "distinct ys" "distinct xs"
    thus "length xs = length ys" by (metis distinct_card)
    next
    assume "set xs = set ys" "distinct ys" "length xs = length ys"
    thus "distinct xs" by (metis card_distinct distinct_card)
  qed
    
  lemma distinct_by_mergesort: "(length (mergesort_remdups xs) = length xs) \<longleftrightarrow> distinct xs"
   proof -
   from mergesort_remdups_correct have 1: "set xs = set (mergesort_remdups xs)" by fastforce
   from list_length_iff_distinct[OF 1] mergesort_remdups_correct have 
    "length xs = length (mergesort_remdups xs) \<longleftrightarrow> distinct xs" by fastforce
   from this show ?thesis by fastforce
  qed

  lemma [code]: "distinct xs = (length (mergesort_remdups xs) = length xs)"
  by(simp add:distinct_by_mergesort)

  
  text{*providing tail recursive versions of certain functions*}
  (*otherwise scala code generated with this code always produces a StackOverflowException for large inputs*)

  text{*List.map*}
  fun map_tailrec ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "map_tailrec f [] accs = accs" | 
  "map_tailrec f (a#as) accs = (map_tailrec f as ((f a)#accs))"

  lemma map_tailrec_is_listmap: 
  "rev (map_tailrec f l accs) = (rev accs)@(List.map f l)"
    apply(induction l accs rule: map_tailrec.induct)
    apply(simp_all)
    done

  definition efficient_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
    "efficient_map f l \<equiv> rev (map_tailrec f l [])"

  lemma[code]: "List.map f l = efficient_map f l"
   by(simp add: efficient_map_def map_tailrec_is_listmap)

   text{*ListAdd.merge*}
   (*inefficient version*)
   fun merge_tailrec_inefficient :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
      "merge_tailrec_inefficient (a#as) (b#bs) accs = (if a < b
        then merge_tailrec_inefficient (as) (b#bs) (accs@[a])
        else if a = b then merge_tailrec_inefficient (as) (bs) (accs@[a])
        else merge_tailrec_inefficient (a#as) (bs) (accs@[b]))"
    | "merge_tailrec_inefficient [] bs accs= accs@bs"
    | "merge_tailrec_inefficient as [] accs = accs@as"

    lemma merge_tailrec_inefficient_prepend:
    "merge_tailrec_inefficient as bs (a # accs) = a # merge_tailrec_inefficient as bs accs"
      apply(induction as bs accs rule: merge_tailrec_inefficient.induct)
      apply(simp)
      apply(simp)
      apply(simp)
      done

    lemma merge_as_tailrec_inefficient: "merge as bs = merge_tailrec_inefficient as bs []"
      apply(induction as bs rule: merge.induct)
      apply(simp_all add:merge_tailrec_inefficient_prepend)
    done


   fun merge_tailrec :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
      "merge_tailrec (a#as) (b#bs) accs = (if a < b
        then merge_tailrec (as) (b#bs) (a#accs)
        else if a = b then merge_tailrec (as) (bs) (a#accs)
        else merge_tailrec (a#as) (bs) (b#accs))"
    | "merge_tailrec [] bs accs= (rev accs)@bs"
    | "merge_tailrec as [] accs = (rev accs)@as"

    lemma merge_tailrec_listappend: 
    "merge_tailrec as bs (accs1@accs2) = (rev accs2)@(merge_tailrec as bs accs1)"
      apply(induction as bs "accs1@accs2" arbitrary: accs1 accs2 rule: merge_tailrec.induct)
      apply(simp_all)
      apply(case_tac "a < b")
      apply(simp)
      apply (metis append_Cons)
      apply(case_tac "a = b")
      apply (simp)
      apply (metis append_Cons)
      apply (metis append_Cons)
    done
      
    lemma merge_tailrec_acc_append: 
    "merge_tailrec as bs (accs@[a]) = a#(merge_tailrec as bs (accs))"
      apply(induction as bs accs rule: merge_tailrec.induct)
      apply(simp_all)
    done
    
    lemma merge_inefficient_as_efficient:
    "merge_tailrec_inefficient as bs (rev accs) = (merge_tailrec as bs accs)"
      apply(induction as bs accs arbitrary: accs rule: merge_tailrec_inefficient.induct)
      apply(simp_all)
      apply(case_tac "a < b")
      apply(simp)
      apply (metis rev.simps(2))
      apply(case_tac "a = b")
      apply (metis rev.simps(2))
      apply (metis rev.simps(2))
     done


    lemma[code]: "merge as bs = merge_tailrec as bs []"
      apply(simp add: merge_as_tailrec_inefficient)
      apply(simp add: merge_inefficient_as_efficient[of "as" "bs" "[]", simplified])
    done




(*import scala.annotation.tailrec*)
  export_code distinct in Scala


  value[code] "distinct [(CHR ''A'')]"
  value[code] "distinct [''a'', ''b'']"
  value[code] "distinct [(''a'', ''b'')]" 
  value[code] "distinct (map fst [(''a'', ''b''), (''a'', ''c'')])"

end
