package cfa

import common.AssignOp.OpAssign
import common.{AssignExpr, AssignOp, BlockStmt, BoolLit, BreakStmt, ContinueStmt, EmptyStmt, ExprStmt, Expression, FuncCall, FunctionDecl, FunctionExpr, IfStmt, InfixExpr, LVarRef, NullLit, NumberLit, ReturnStmt, Script, Statement, StringLit, VarDeclListStmt, VarDeclStmt, VarRef, WhileStmt}

//we have to use info from CPA2 paper figure 7.

//u(e,ψ,tf,h)={e}Lam?(e)tf(e)S?(ψ,e)h(e)H?(ψ,e)[ ̃UEA]
// ([[(f eq)l]],tf,h)≈>(ulam,ˆd,h)ulam∈ ̃Au(f,l,tf,h)ˆd = ̃Au(e,l,tf,h)[ ̃UAE]
// ([[(λl(uk)call)]],ˆd,h)≈>(call,[u7→ˆd],h′)h′={ht[u7→ˆd]H?(u)hS?(u)[ ̃CEA]
// ([[(clame)γ]],tf,h)≈>(clam,ˆd,tf,h)ˆd = ̃Au(e,γ,tf,h)[ ̃CAE]
// ([[(λγ(u)call)]],ˆd,tf,h)≈>(call,tf′,h′)tf′=tf[u7→ˆd]h′={ht[u7→ˆd]H?(u)hS?(u)Local domains: ̃Eval=Call× ̃Stack×Heap
// ̃UApply=ULam×̂UClos×Heap ̃CApply=̂CClos×̂UClos× ̃Stack×Heap ̃Frame=UVar⇀̂UClos ̃Stack= ̃FrameAbstract to local maps:
// |(call,st,h)|al= (call,|st|al,h)|(ulam,ˆd,ˆc,st,h)|al= (ulam,ˆd,h)|(ˆc,ˆd,st,h)|al=
// (ˆc,ˆd,|st|al,h)|tf::st′|al={(u,tf(u)) :UVar?(u)}|〈〉|al=∅Figure 7:  Local semantics

object CPA2 {
  var var_count = 0
  def gensym(x: String) = { var_count = var_count + 1; x + var_count }
  var lab_count = 0
  def label = { lab_count = lab_count + 1; lab_count }
  def halt = KVar("halt")

  def t_k (stmts: List[Statement], kmap: Map[String, AExp => CExp], k: AExp => CExp): CExp =
    stmts match {
      case Nil => k(Void)
      case List(stmt) => t_k(stmt, kmap, k)
      case stmt::stmts => t_k(stmt, kmap, (_ : AExp ) => t_k (stmts, kmap, k))
    }

  // if 'k' is 'x => c(x)', then 'h(c)' else 'let c = x => k(x) in h(c)'
  def check_tail(x: UVar, k: AExp => CExp, h: KVar => CExp) = {
    k(x) match {
      case KApp(c@KVar(_), y, _) if x == y => h(c)
      case _ => {
        val c = KVar(gensym("k"))
        KLet(c, KLam(x, k(x)), h(c))
      }
    }
  }

  def t_k (stmt: Statement, kmap: Map[String, AExp => CExp], k: AExp => CExp): CExp = {
    stmt match {
      case Script(stmts) => t_k(BlockStmt(stmts), kmap, k)
      case BlockStmt(stmts) => {
        val (funs, rest) = stmts.foldRight((List[FunctionDecl](), List[Statement]()))((stmt, c) =>
          stmt match {
            case f:FunctionDecl => (f::c._1, c._2)
            case _ => (c._1, stmt::c._2)
          }
        )
        val fs = funs.map(fun => Fun(UVar(fun.name.str), m(fun.fun).asInstanceOf[ULam]))
        val e = t_k(rest, kmap, k)
        if (fs.isEmpty) e else Begin(fs, e)
      }
      case BreakStmt(_) => kmap("break")(Void)       // ignore label for now
      case ContinueStmt(_) => kmap("continue")(Void) // ignore label for now
      case ReturnStmt(e) => t_k(e, x => kmap("return")(x))
      case VarDeclStmt(x, e) => {
        val y = UVar(x.str)
        t_k_prim(e, z => ULet(y, z, k(y)))
      }
      case VarDeclListStmt(decls) => t_k(decls, kmap, k)
      case IfStmt(cond, thenPart, elsePart) => {
        val h = (c: KVar) => t_k(cond, b => If(b, t_c(thenPart, kmap, c), t_c(elsePart, kmap, c)))
        check_tail(UVar(gensym("_")), k, h)
      }
      case ExprStmt(e) => t_k(e, k)

      case EmptyStmt() => k(Void)

      case WhileStmt(cond, stmt) => {
        val lk = KVar(gensym("k"))
        val x = UVar(gensym("_"))
        val recur = KApp(lk, Void, label)
        val kmap1 = kmap + ("continue" -> ((x:AExp) => KApp(lk, x, label))) + ("break" -> k)
        val loop = t_k(cond, b => If(b, t_c(stmt, kmap1, lk), k(Void)))
        KLet(lk, KLam(x, loop), recur)
      }

      case _ => throw new Exception("wrong argument in call to t_k: " + stmt)
    }
  }

  def t_k (exp: Expression, k: AExp => CExp): CExp =
    exp match {
      case InfixExpr(op, e1, e2) => t_k_prim(exp, x => {
        val y = UVar(gensym("u"))
        ULet(y, x, k(y))
      })
      case AssignExpr(op, LVarRef(x1), e2) => {
        val y = UVar(x1)
        op match {
          case OpAssign => t_k_prim(e2, x2 => Update(y, x2, k(y)))
          case _ => t_k(e2, x2 => Update(y, Prim(AssignOp.toOp(op), y, x2), k(y)))
        }
      }
      case FuncCall(f, as) => {
        val h = (c: KVar) => t_k(f, fx => t_ks(as, xs => UApp(fx, xs, c, label)))
        check_tail(UVar(gensym("x")), k, h)
      }
      case _ => k(m(exp))
    }

  def t_ks (es: List[Expression], k: List[AExp] => CExp): CExp =
    es match {
      case Nil => k(Nil)
      case e::es => t_k(e, x => t_ks(es, xs => k(x::xs)))
    }

  def t_k_prim (exp: Expression, k: BExp => CExp): CExp =
    exp match {
      case InfixExpr(op, e1, e2) => t_k(e1, x1 => t_k(e2, x2 => k(Prim(op, x1, x2))))
      case _ => t_k(exp, k)
    }

  def t_c (stmt: Statement, kmap: Map[String, AExp => CExp], c: KVar): CExp = t_k(stmt, kmap, (x : AExp) => KApp(c, x, label))

  def t_c (exp: Expression, c: KVar): CExp = t_k(exp, x => KApp(c, x, label))

  def m (exp: Expression): AExp =
    exp match {
      case NumberLit(x) => Num(x)
      case StringLit(x) => Str(x)
      case BoolLit(x) => Bool(x)
      case NullLit() => Void
      case VarRef(x) => UVar(x)
      case FunctionExpr(_, ps, body) => {
        val xs = ps.map(p => UVar(p.str))
        val c = KVar(gensym("k"))
        ULam(xs, c, t_c(body, Map("return" -> ((x:AExp)=>KApp(c, x, label))), c))
      }
      case _ => throw new Exception("wrong argument in call to m: " + exp)
    }
}
