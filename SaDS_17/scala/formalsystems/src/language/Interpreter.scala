package language

/** interpretN interprets all terms in object of non-terminal N
 *  
 * precondition: input must be well-formed (Checker.checkN)
 */
object Interpreter {  
  
  /** run-time errors */
  case class Error(msg: String) extends java.lang.Exception(msg)
  
  // interpret all value definitions in order
  def interpretContext(context: Context, c: Context): Context = {
    val declsI = interpretDeclList(context, c.decls, Nil)
    Context(declsI)
  }

  // auxiliary functions of interpretContext
  private def interpretDeclList(context: Context, decls: List[Decl], sofar: List[Decl]): List[Decl] = decls match {
    case Nil => sofar.reverse
    case hd::tl =>
      val hdI = interpretDecl(context, hd)
      interpretDeclList(context.and(hdI), tl, hdI::sofar)
  }
  
  // interpret the definition of a value
  def interpretDecl(context: Context, decl: Decl): Decl = decl match {
    case Val(x,a,vOpt) => vOpt match {
      case Some(v) =>
        val vI = interpretTerm(context, v)
        Val(x,a,Some(vI))
      case None =>
        Val(x,a,None)
    }
    
    // ***************************
    case TypeDecl(a) => decl
    case IDTDecl(a, cs) => decl  // no term in constructors
    case ADTDecl(a, fs) => decl  // no term in fields
    case Command(tm) =>
      val tmI = interpretTerm(context, tm)
      Command(tmI) // can usually be thrown away
    case Var(x, aO, v) =>
      val vI = interpretTerm(context, v)
      val loc = new Location(x, aO.get, vI) //TODO check this
      val ltO = aO.map(a => LocationType(a))
      Val(x, ltO, Some(loc))
  }
  
  // interpret a term by expanding all definitions and running functions
  def interpretTerm(context: Context, tm: Term): Term = tm match {
    case TermRef(n) =>
      context.get(n) match {
        // replace n with its definition
        case Some(d) => d match {
          case Val(_,_,vOpt) => vOpt match {
            case Some(v) => interpretTerm(context, v)
            case None => tm
          }
          case Command(_) =>
            throw Error("unexpected command") // impossible because commands are anonymous
          case Var(_,_,_) =>
            throw Error("unexpected variable declaration: " + n.name) // impossible because interpretDecl turns Var's into Val's
          case _: ADTDecl | _: IDTDecl | _: TypeDecl =>
            throw Error("not a term") // impossible for well-formed terms
        }
        case None =>
          throw Error("unknown name: " + n.name) // impossible for well-formed terms
      }
    // nothing to do for literals
    case UnitLit() | IntLit(_) | BoolLit(_) => tm
    // apply operators: interpret all arguments left to right; if that returns only literals, apply the corresponding Scala operator
    case Operator(op, args) =>
      // TODO short-circuit evaluation
      val argsI = args.map(a => interpretTerm(context, a))
      val tmI = Operator(op, argsI)
      tmI match {
        case Operator("==", List(a,b)) => BoolLit(a == b)
        case Operator("!=", List(a,b)) => BoolLit(a != b)
        case Operator(op, List(IntLit(i),IntLit(j))) =>
          op match {
            case "+" => IntLit(i+j)
            case "-" => IntLit(i-j)
            case "*" => IntLit(i*j)
            case "mod" => IntLit(i % j)
            case "div" => IntLit(i / j)
            case "<=" => BoolLit(i <= j)
            case ">=" => BoolLit(i >= j)
            case "<" => BoolLit(i < j)
            case ">" => BoolLit(i > j)
          }
        case Operator(op, List(BoolLit(b), BoolLit(c))) =>
          op match {
            case "&&" => BoolLit(b && c)
            case "||" => BoolLit(b || c)
          }
        case _ => tmI //TODO
      }
      
    case LocalDecl(d, t) =>
      val dI = interpretDecl(context, d)
      val tI = interpretTerm(context.and(dI), t)
      // true if we can contract the local declaration because it is not referred to anymore
      val canContract = d match {
        case Val(_,_,vOpt) => vOpt.isDefined // defined Val's have been expanded in tI
        // ***********************
        case Var(_,_,_) => true              // Var's have become defined Val's in dI
        case Command(_) => true              // Command's can never be referred to anyway
        case TypeDecl(_) => false
        case IDTDecl(_,_) => false
        case ADTDecl(_,_) => false
      }
      if (canContract) {
         tI
      } else {
         LocalDecl(dI, tI)
      }

    // this part is very difficult; the behavior given here is just a very simple solution; there is lots of research on how to do it better
    // in particular, if side-effects are possible, we must not interpret the body of a function before it is called

    case Lambda(x,aO,t) =>
      // cannot evaluate a function recursively
      // instead, close it by expanding all references to the context
      val tI = Closer.closeTerm(context.and(Val(x,aO,None)), t) // type is always present for checked terms
      Lambda(x,aO,tI)

    case Apply(fun,arg) =>
      // if the function is a Lambda, define its argument variable and interpret the body
      val funI = interpretTerm(context, fun)
      val argI = interpretTerm(context, arg)
      funI match {
        case Lambda(x,aO,t) =>
          interpretTerm(context.and(Val(x,aO,Some(argI))), t)
        case _ => Apply(funI, argI) // should not happen
      }
      
    // ********************************
    case ConsApply(c, arg) =>
      ConsApply(c, interpretTerm(context, arg))
    case Match(t, cases) =>
      val tI = interpretTerm(context, t)
      tI match {
        case ConsApply(con, arg) =>
          cases.find(c => c.name == con) match {
            case Some(cas) =>
              interpretTerm(context.and(Val(cas.patvar, cas.argType, Some(arg))), cas.body)
            case None =>
              throw Error("missing case in pattern-match") // impossible for well-formed terms
          }
        case _ => Match(tI, cases) // should not happen
      }
    case New(a, defs) =>
      val asContext = defs.map(d => Var(d.name, d.tp, d.definition))
      val defsI = interpretContext(context, Context(asContext))
      Instance(a, defsI)
    case Instance(_,_) => tm
      
    case FieldAccess(t, f) =>
      val tI = interpretTerm(context, t)
      tI match {
        case Instance(a, defs) =>
          interpretTerm(context.and(defs.decls), TermRef(f))
        case _ => FieldAccess(tI, f) // should not happen
      }

    // ********************************
    case loc: Location =>
      loc.value
    case Assignment(x, v) =>
      val loc = x match {
        case TermRef(n) =>
          context.get(n) match {
            case Some(Val(_,_,Some(l:Location))) => l
            case None => throw Error("unknown assignment target: " + n.name) // impossible for well-formed terms
            case _ => throw Error("unexpected assignment target: " + n.name)
          }
        case loc: Location => loc
        case l => throw Error("unexpected assignment target") // impossible for well-formed terms  
      }
      loc.value = interpretTerm(context, v)
      UnitLit()
    case While(c,b) =>
      while (interpretTerm(context,c) == BoolLit(true)) {
        interpretTerm(context, b)
      }
      UnitLit()
    case Print(t) =>
      val tI = interpretTerm(context, t)
      println(Printer.printTerm(tI))
      UnitLit()
  }
}

// *********************************************************************

/** recursively replaces every TermRef with its definition
 *
 * precondition: input is well-formed
 * postcondition: output does not refers to context for defined Val declarations
 */
object Closer {
  def closeDecl(context: Context, decl: Decl): Decl = decl match {
    case Val(x,a,vOpt) =>
      val vC = vOpt match {
        case Some(v) => Some(closeTerm(context, v))
        case None => None
      }
      Val(x, a, vC)
    case TypeDecl(_) => decl
    case ADTDecl(a, fs) => decl  // no terms may occur in fields at this point
    case IDTDecl(a, cs) => decl  // no terms may occur in constructors at this point
    case Command(tm) => 
      val tmC = closeTerm(context, tm)
      Command(tmC)
    case Var(x,a,v) =>
      val vC = closeTerm(context, v)
      Var(x,a,vC)
  }
  
  // replace all references to the context with their definition
  def closeTerm(context: Context, tm: Term): Term = tm match {
    case TermRef(n) =>
      context.get(n) match {
        case Some(d) => d match {
          case Val(_,_,Some(v)) => closeTerm(context, v) // recursion needed in case v is a function
          case _ => tm
        }
        case None => tm // impossible for well-formed terms
      }
    // nothing to do for literals
    case UnitLit() | IntLit(_) | BoolLit(_) => tm
    // apply operators: close all arguments left to right; if that returns only literals, apply the corresponding Scala operator
    case Operator(op, args) =>
      val argsC = args.map(a => closeTerm(context, a))
      Operator(op, argsC)
      
    case LocalDecl(d, t) =>
      val dC = closeDecl(context, d)
      val tC = closeTerm(context.and(dC), t)
      LocalDecl(dC, tC)

    case Lambda(x,aO,t) =>
      val tC = closeTerm(context.and(Val(x,aO,None)), t)
      Lambda(x,aO,tC)
    case Apply(fun,arg) =>
      // if the function is a Lambda, define its argument variable and close the body
      val funC = closeTerm(context, fun)
      val argC = closeTerm(context, arg)
      Apply(funC, argC)

    case ConsApply(c, arg) => ConsApply(c, closeTerm(context, arg))
    case Match(t, cases) =>
      val tC = closeTerm(context, t)
      val casesC = cases.map {c =>
        val bodyC = closeTerm(context.and(Val(c.patvar, c.argType, None)), c.body)
        ConsCase(c.name, c.patvar, c.argType, bodyC)
      }
      Match(tC, casesC)
    case New(a, defs) =>
      val defsC = defs.map {d =>
        FieldDef(d.name, d.tp, closeTerm(context, d.definition))
      }
      New(a, defsC)
    case Instance(a, defs) => tm
    
    case FieldAccess(t, f) => FieldAccess(closeTerm(context, t), f)

    case loc: Location =>
      loc
    case Assignment(x,v) =>
      val xC = closeTerm(context, x)
      val vC = closeTerm(context, v)
      Assignment(xC,vC)
    case While(c,b) =>
      val cC = closeTerm(context, c)
      val bC = closeTerm(context, b)
      While(cC,bC)
    case Print(t) =>
      val tC = closeTerm(context, t)
      Print(tC)
  }
}