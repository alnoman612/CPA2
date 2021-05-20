package cfa
import common._
import java.io.File

import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}

object Time { var k = 0 }

trait Term {
  override def toString = this match {
    case Time(lst) => s"[${lst.mkString(" ")}]"
    case Cls(lam, env) => s"cls((${lam.xs.mkString(", ")}, ${lam.k}) =>, $env)"
    case AVal(cls) => s"{${cls.mkString(", ")}}"
    case KFrame(klam, env, kenv) => s"frame((${klam.x}) =>, $env, $kenv)" 
    case Halt => "halt"
    case ACont(frames) => s"{${frames.mkString(", ")}}"
    case Addr(x, t) => s"($x, $t)"
    case KAddr(x, t) => s"($x, $t)"
    case Env(map) => s"[${map.mkString(", ")}]"
    case KEnv(map) => s"[${map.mkString(", ")}]"
    case Store(map) => s"value store:\n${map.mkString("\n")}"
    case KStore(map) => s"continuation store:\n${map.mkString("\n")}"
  }
}

case class Time(lst: List[Int]) extends Term {
  def + (l: Int) = {
    val lst1 = lst ++ List(l)
    
    Time(if (lst1.length > Time.k) lst1.tail else lst1)
  } 
}

case class Cls(lam: ULam, env: Env) extends Term // user lambda closure 

case class AVal(cls: Set[Cls]) extends Term { // abstract values
  def + (v: AVal) = AVal(cls ++ v.cls) 
}

trait Frame extends Term // abstract frame
case class KFrame(klam: KLam, env: Env, kenv: KEnv) extends Frame // continuation frame 
object Halt extends Frame // special frame for termination 

case class ACont(frames: Set[Frame]) extends Term { // abstract continuations
  def + (f: ACont) = ACont(frames ++ f.frames) 
} 

case class Addr(x: UVar, t: Time) extends Term // abstract value store address

case class KAddr(x: KVar, t: Time) extends Term // abstract continuation store address

case class Env(map: Map[UVar, Addr]) extends Term { // binding environment for user variables 
  def + (x: UVar, a: Addr) = Env(map + (x -> a))
  def apply(x: UVar) = map(x)
}
case class KEnv(map: Map[KVar, KAddr]) extends Term { // binding environment for continuation variables
  def + (x: KVar, a: KAddr) = KEnv(map + (x -> a))
  def apply(x: KVar) = map(x)
} 

case class Store(map: MMap[Addr, AVal]) extends Term { // store for abstract values 
  def + (a: Addr, v: AVal) = { 
    map.get(a) match { 
      case Some(v1) => map += (a -> (v1 + v))
      case None => map += (a -> v)
    }
    this
  }
  def apply(x: Addr) = map(x)
}

// KVar("halt") is not in the continuation store.
case class KStore(map: MMap[KAddr, ACont]) extends Term { // store for abstract continuations
  def + (a: KAddr, c: ACont) = {
    map.get(a) match { 
      case Some(c1) => map += (a -> (c1 + c))
      case None => map += (a -> c)
    }
    this
  }
  def apply(x: KAddr) = map(x)
}
// use mutable value/continuation stores -- in effect, stores are global (not per-state).
case class State(e: CExp, env: Env, kenv: KEnv, time: Time, store: Store, kstore: KStore) {
  def next : List[State] = {
    
    def eval (e: BExp) = e match {
      case x:UVar => store(env(x))
      case lam:ULam => AVal(Set(Cls(lam, env)))
      case _ => AVal(Set())
    }
    
    e match {
      case KLet(x, klam, e2) => {
        val a = KAddr(x, time)
        val kenv1 = kenv + (x, a)
        val kstore1 = kstore + (a, ACont(Set(KFrame(klam, env, kenv1))))
        List(State(e2, env, kenv1, time, store, kstore1))    
      }
      case ULet(x, e1, e2) => {
        val v = eval(e1)
        val a = Addr(x, time)
        List(State(e2, env + (x, a), kenv, time, store + (a, v), kstore))
      }
      case Update(x, e1, e2) => { 
        List(State(e2, env, kenv, time, store + (env(x), eval(e1)), kstore))
      }
      case If(b, e1, e2) => {
        List(State(e1, env, kenv, time, store, kstore), State(e2, env, kenv, time, store, kstore))
      }
      case KApp(k, e, label) => { 
          for {
              f <- kstore(kenv(k)).frames.toList if f != Halt
              val KFrame(KLam(x, e1), env1, kenv1) = f
              val time1 = time + label
              val a = Addr(x, time1)
          } 
          yield(State(e1, env1 + (x, a), kenv1, time1, store + (a, eval(e)), kstore))
      }
      
      case UApp(f, args, c, label) => { 
        for {
            Cls(ULam(xs, k, e0), env0) <- eval(f).cls.toList
            val (la, lx) = (args.length, xs.length)
            // take care of unmatched arguments or parameters
            val args1 = if(la < lx) args ++ List.range(0, lx - la) map(_ => Void)
                        else if (la > lx) args.take(lx) else args
                        
            val time1 = time + label
            val as = xs map (x => Addr(x, time1))  
            val vs = args1 map (arg => eval(arg))
            val env1 = (xs zip as).foldLeft(env0)((benv: Env, xa: (UVar, Addr)) => benv + (xa._1, xa._2))
            val store1 = (as zip vs).foldLeft(store)((sr: Store, av: (Addr, AVal)) => sr + (av._1, av._2))
            val ka = KAddr(k, time1)
        }
        yield (State(e0, env1, kenv + (k, ka), time1, store1, kstore + (ka, kstore(kenv(c)))))
      }
      
      case Begin(fs, e) => {
        val (ns, lams) = (for(Fun(f, lam) <- fs) yield (f, lam)).unzip
        val as = ns map (n => Addr(n, time))
        val env1 = (ns zip as).foldLeft(env)((ev, na) => ev + (na._1, na._2))
        val store1 = (as zip lams).foldLeft(store)((sr, al) => store + (al._1, AVal(Set(Cls(al._2, env1)))))
        List(State(e, env1, kenv, time, store1, kstore))
      }
    }
  }
}

case class ST(e: CExp, env: Env, kenv: KEnv, time: Time) {
  override def toString = (e match {
    case KLet(k,KLam(x,_),_) => s"let $k = $x => ..."
    case ULet(f,ULam(xs,k,_),_) => s"let $f = (${xs.mkString(", ")}, $k) => ..."
    case ULet(x,e1,_) => s"let $x = $e1"
    case Update(x,e1,_) => s"$x = $e1"
    case If(b,_,_) => s"if ($b) ..."
    case KApp(k,arg,l) => s"$l: $k($arg)"
    case UApp(f,args,c,l) => s"$l: $f(${args.mkString(", ")}, $c)"
    case Begin(fs,_) => fs.map(f => s"function ${f.f} (${f.lam.xs.mkString(", ")}, ${f.lam.k}) {...}").mkString("\\n")
    case _ => e.toString
  }) // replace special tokens so that dotgraph can render nicely
  .replaceAll("\\<", "\\\\<")
  .replaceAll("\\>", "\\\\>")
  .replaceAll("\\{", "\\\\{")
  .replaceAll("\\}", "\\\\}")
}

object CFA {
  def explore (e: CExp) = {
    val t0 = Time(Nil)
    val a = KAddr(CPS.halt, t0)
    def s0 = State(e, Env(Map()), KEnv(Map(CPS.halt -> a)), t0, Store(MMap()), KStore(MMap(a -> ACont(Set(Halt)))))
  
    // worklist algorithm
    var todo = List(s0)
    val seen = MSet[State]()
    
    val edges = MMap[ST, MSet[ST]]()
    
    while(!todo.isEmpty) {
      val s1 = todo.head
      todo = todo.tail
      if (!seen.contains(s1)) {
        seen += s1
        val states = s1.next 
        todo = states ++ todo
        addStatePair(edges, ST(s1.e, s1.env, s1.kenv, s1.time), states map (s => ST(s.e, s.env, s.kenv, s.time)))
      }
    }
    (seen, edges)
  }
  
  def addStatePair(map: MMap[ST, MSet[ST]], s1: ST, s2: List[ST]) {
    if (! map.contains(s1)) map.put(s1, MSet[ST]())   
    val set = map(s1)
    set ++= s2
  }
  
  def main(args: Array[String]) { 
    Time.k = 0
    
    val ast = GenerateAST(new File("test/twice.js"))
    val cps = CPS.t_c(ast, Map(), CPS.halt)  
    val (seen, edges) = explore(cps)
    println(seen.size)
    println(seen.head.store)
    println(seen.head.kstore)
    
    val lst = edges.keys.toList    
    val map = (lst zipWithIndex) toMap

    println("\ndigraph g {\nnode [shape = record,height=.1];")
    val nodes = (lst map (n => s"${map(n)}[label = ${'"'}$n${'"'}]")).mkString(";\n")   
    println(nodes)
    for(s1 <- lst) {
      for(s2 <- edges(s1)) {
        s1 match {
          case ST(_:UApp,_,_,_) => print(s"${map(s1)} -> ${map(s2)} [style=bold]; ") 
          case ST(_:KApp,_,_,_) => print(s"${map(s1)} -> ${map(s2)} [style=solid]; ") 
          case _ => print(s"${map(s1)} -> ${map(s2)} [style=dotted]; ") 
        }
      } 
      println
    }
    
    println("}")
  }
}




