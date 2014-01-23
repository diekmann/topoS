package tum.in.net.psn.log_topo

import NetworkModels.GENERATED

/**
 * This object provides the necessary equal operator for the generated graph type
 * 
 * vertices of graph are strings
 * setup of equal trait
 */
object HOLequal_String {
  implicit def equal_string_tuple: GENERATED.HOL.equal[(String, String)] = new GENERATED.HOL.equal[(String, String)] {
    val `HOL.equal` = (a: (String, String), b: (String, String)) => a == b
  }
  implicit def equal_String: GENERATED.HOL.equal[String] = new GENERATED.HOL.equal[String] {
      val `HOL.equal` = (a: String, b: String) => (a == b)
  }
  implicit def vertices_String: GENERATED.NetworkModel_Vertices.vertex[String] = new GENERATED.NetworkModel_Vertices.vertex[String] {
    val `NetworkModel_Vertices.vertex_1` = "vertex_1_String"
    val `NetworkModel_Vertices.vertex_2` = "vertex_2_String"
    val `NetworkModel_Vertices.vertex_3` = "vertex_3_String"
  }
  
  
  //  implicit def equal_list[A : GENERATED.HOL.equal]: GENERATED.HOL.equal[List[A]] = new
  //    GENERATED.HOL.equal[List[A]] {
  //  val `HOL.equal` = (a: List[A], b: List[A]) => GENERATED.Lista.equal_lista[A](a, b)
  //  }
  
  implicit def equal_prod[A : GENERATED.HOL.equal, B : GENERATED.HOL.equal]: GENERATED.HOL.equal[(A, B)] = new
    GENERATED.HOL.equal[(A, B)] {
    val `HOL.equal` = (a: (A, B), b: (A, B)) => GENERATED.Product_Type.equal_proda[A, B](a, b)
  }
  
  implicit def
    ord_prod[A : GENERATED.HOL.equal : GENERATED.Orderings.ord, B : GENERATED.HOL.equal : GENERATED.Orderings.ord]:
      GENERATED.Orderings.ord[(A, B)]
    = new GENERATED.Orderings.ord[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_prod[A, B](a, b)
  }
  
  implicit def
    preorder_prod[A : GENERATED.HOL.equal : GENERATED.Orderings.order,
                   B : GENERATED.HOL.equal : GENERATED.Orderings.order]:
      GENERATED.Orderings.preorder[(A, B)]
    = new GENERATED.Orderings.preorder[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_prod[A, B](a, b)
  }
  
  implicit def
    order_prod[A : GENERATED.HOL.equal : GENERATED.Orderings.order, B : GENERATED.HOL.equal : GENERATED.Orderings.order]:
      GENERATED.Orderings.order[(A, B)]
    = new GENERATED.Orderings.order[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_prod[A, B](a, b)
  }
  
  implicit def
    linorder_prod[A : GENERATED.HOL.equal : GENERATED.Orderings.linorder,
                   B : GENERATED.HOL.equal : GENERATED.Orderings.linorder]:
      GENERATED.Orderings.linorder[(A, B)]
    = new GENERATED.Orderings.linorder[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) => GENERATED.Misc.less_prod[A, B](a, b)
  }
  
  
  implicit def ord_string: GENERATED.Orderings.ord[String] = new GENERATED.Orderings.ord[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  
  implicit def preorder_string: GENERATED.Orderings.preorder[String] = new
    GENERATED.Orderings.preorder[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  
  implicit def order_string: GENERATED.Orderings.order[String] = new GENERATED.Orderings.order[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  
  implicit def linorder_string: GENERATED.Orderings.linorder[String] = new
    GENERATED.Orderings.linorder[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  
  
  
  implicit def ord_list[A : GENERATED.HOL.equal : GENERATED.Orderings.order]: GENERATED.Orderings.ord[List[A]] =
    new GENERATED.Orderings.ord[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_list[A](a, b)
  }
  
  implicit def
    preorder_list[A : GENERATED.HOL.equal : GENERATED.Orderings.order]: GENERATED.Orderings.preorder[List[A]] =
    new GENERATED.Orderings.preorder[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_list[A](a, b)
  }
  
  implicit def
    order_list[A : GENERATED.HOL.equal : GENERATED.Orderings.order]: GENERATED.Orderings.order[List[A]] = new
    GENERATED.Orderings.order[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_list[A](a, b)
  }
  
  implicit def
    linorder_list[A : GENERATED.HOL.equal : GENERATED.Orderings.linorder]: GENERATED.Orderings.linorder[List[A]]
    = new GENERATED.Orderings.linorder[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) => GENERATED.List_lexord.less_list[A](a, b)
  }
  
  
  type Node = String
}