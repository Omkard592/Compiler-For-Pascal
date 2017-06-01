/****************************************************************************************************
 *
 * File: Code.scala
 * The IR code generator for PCAT programs
 *
 ****************************************************************************************************/

package edu.uta.pcat

import scala.collection.mutable.Stack

abstract class CodeGenerator ( tc: TypeChecker )  {
  def typechecker = tc
  def st = tc.st
  def code ( e: ProcDecl ): IRstmt
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp
}


class Code ( tc: TypeChecker ) extends CodeGenerator(tc) {

  /** holds the exit labels of loops (needed for the exit() statements) */
  var labels = new Stack[String]

  var name_counter = 0

  /** generate a new variable name */
  def new_name ( name: String ): String = {
    name_counter += 1
    name + "_" + name_counter
  }

  /** allocate a new variable at the end of the current frame and return the access code */
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp = {
    st.lookup(fname) match {
      case Some(ProcDec(rtp,params,label,level,min_offset)) => {
          // allocate variable at the next available offset in frame
          st.insert(name,VarDec(var_type,level,min_offset))
          // the next available offset in frame is 4 bytes below
          st.replace(fname,ProcDec(rtp,params,label,level,min_offset-4))
          // return the code that accesses the variable
          Mem(Binop("PLUS",Reg("fp"),IntValue(min_offset)))
      }
      case _ => throw new Error("No current function: " + fname)
    }
  }

  /** access a frame-allocated variable from the run-time stack */
  def access_variable ( name: String, level: Int ): IRexp = {
    st.lookup(name) match {
      case Some(VarDec(_,var_level,offset)) => {
        var res: IRexp = Reg("fp")
        // non-local variable: follow the static link (level-var_level) times
        for ( i <- var_level+1 to level )
            res = Mem(Binop("PLUS",res,IntValue(-8)))
        Mem(Binop("PLUS",res,IntValue(offset)))
      }
      case _ => throw new Error("Undefined variable: " + name)
    }
  }

  /** return the IR code from the Expr e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Expr, level: Int, fname: String ): IRexp = {
    e match {
      case BinOpExp(op,left,right) => {
          val cl = code(left,level,fname)
          val cr = code(right,level,fname)
          val nop = op.toUpperCase()
          Binop(nop,cl,cr)
      }
	  
	  case UnOpExp(op,exp) => {
          val cl = code(exp,level,fname)
          
          val nop = op.toUpperCase()
          Unop(nop,cl)
      }
	  
	  
      case ArrayExp(nm,inits) => {
        // A is the array address
        val A = allocate_variable(new_name("A"),NamedType(nm),fname)
        // I is offset of end-of-array
        val I = allocate_variable(new_name("I"),typechecker.intType,fname)
        // for iterating through loops
        val i = allocate_variable(new_name("i"),typechecker.intType,fname)
        // IR that calculates the array length
        var len: IRexp = IntValue(0)
        var cs: List[IRstmt] = List()
        for ( (n,v) <- inits )
          if (n == IntConst(1)) {   // don't need a loop for this
              val cv = code(v,level,fname)
              len = Binop("PLUS",len,IntValue(1))
              cs = cs :+ Seq(List(Move(Mem(Binop("PLUS",A,I)),cv),
                                  Move(I,Binop("PLUS",I,IntValue(4)))))
          } else {
            val cn = code(n,level,fname)
            val cv = code(v,level,fname)
            val loop = new_name("loop")
            val exit = new_name("exit")
            len = Binop("PLUS",len,cn)
            cs = cs :+ Seq(List(Move(i,IntValue(0)),
                                Label(loop),          // a for-loop
                                CJump(Binop("GEQ",i,cn),exit),
                                Move(Mem(Binop("PLUS",A,I)),cv),
                                Move(I,Binop("PLUS",I,IntValue(4))),
                                Move(i,Binop("PLUS",i,IntValue(1))),
                                Jump(loop),
                                Label(exit)))
          }
        ESeq(Seq(List(Move(A,Allocate(Binop("PLUS",len,IntValue(1)))),    // allocate len+1 words for A
                      Move(Mem(A),len),         // set the array length
                      Move(I,IntValue(4)))      // first available offset is 4
                 ++ cs),
             A)          
      }

	  
	  
	 case RecordExp(nm,inits) => {
        // A is the array address
        val A = allocate_variable(new_name("A"),NamedType(nm),fname)
        // I is offset of end-of-array
        val I = allocate_variable(new_name("I"),typechecker.intType,fname)
        // for iterating through loops
        val i = allocate_variable(new_name("i"),typechecker.intType,fname)
        // IR that calculates the array length
        var len: IRexp = IntValue(0)
        var cs: List[IRstmt] = List()
        /*for ( (n,v) <- inits ) {
            st.insert(n,VarDec(NamedType("INTEGER"),0,0))
        //    allocate_variable(n,NamedType("STRING"),fname)
            val cv = code(v,level,fname)
            val loop = new_name("loop")
            val exit = new_name("exit")
            len = Binop("PLUS",len,IntValue(4))
            //cs = cs :+ Seq(List(Move(i,IntValue(0)),
                                //Label(loop),          // a for-loop
                                //CJump(Binop("GEQ",i,IntValue(4)),exit),
                                //Move(Mem(Binop("PLUS",A,I)),cv),
                                //Move(I,Binop("PLUS",I,IntValue(4))),
                                //Move(i,Binop("PLUS",i,IntValue(1)))
                                //Jump(loop),
                                //Label(exit)
						//		))
        }*/
        ESeq(Seq(List(Move(A,Allocate(Binop("PLUS",len,IntValue(1)))),    // allocate len+1 words for A
                      Move(Mem(A),len),         // set the array length
                      Move(I,IntValue(4)))      // first available offset is 4
                 ),
             A)          
      }
	 
	 case CallExp(nm, lexp) => {	
					val callee = new_name(nm)
	              var sq_lst: List[IRexp] = List()			
                   sq_lst = for(ei <- lexp)			
                                             yield			
                                            {			
                                                     code(ei, level, fname)			
                                              }			
                //Call(nm,Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),sq_lst)    
					Call(callee,Reg("fp"),sq_lst)
				
     }
	  
	  
	 case LvalExp(l) => l match
	{
		case Var("NIL") =>
		{
			st.insert("NIL",VarDec(AnyType(),0,0))
			code(l,level,fname)
		}
		
		case Var("TRUE") =>
		{
			st.insert("TRUE",VarDec(NamedType("BOOLEAN"),0,0))
			code(l,level,fname);
		}
		
		case Var("FALSE") =>
		{
			st.insert("FALSE",VarDec(NamedType("BOOLEAN"),0,0))
			code(l,level,fname);
		}
		
		case _ =>
		{
			code(l,level,fname);
		}
		
	}
	  
	  
	  
	  //my code
	  case StringConst(s) => {
			StringValue(s)
	  }
	  
	  case IntConst(x) => {
			IntValue(x)
	  }
	  
	  
	  //my code
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong expression: "+e)
    }
  }

  /** return the IR code from the Statement e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Stmt, level: Int, fname: String ): IRstmt = {
    e match {
      case AssignSt(v,u) => {
            val cd = code(v,level,fname)
            val cs = code(u,level,fname)
            Move(cd,cs)
      }

	  
	  //my code

			 case WriteSt(lexp) => {
			var sql: List[IRstmt] = List()
			sql = for (ei <- lexp)
				yield 
				{
					if (typechecker.typecheck(ei).equals(typechecker.stringType))
					
						SystemCall("WRITE_STRING",code(ei,level, fname))
					
					else
					
						SystemCall("WRITE_INT",code(ei,level, fname))
					
				}
				
					
				
			sql = sql :+ SystemCall("WRITE_STRING",code(StringConst("\\n"),level, fname))
			Seq(sql)
	  }




	  case ReadSt(llval) => {
			var ll: List[IRstmt] = List()
			ll = for(li <- llval)
						yield
						{
							SystemCall("READ_INT",code(li,level, fname))
						}
			Seq(ll)
	  }
	  
	   case CallSt(s, lexp) => {
			//st.insert(s,VarDec(NamedType("STRING"),0,0))
			var ll: List[IRexp] = List()
			ll = for(li <- lexp)
						yield
						{
							code(li,level, fname)
							
						}
			
			CallP(s,Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),ll)
			
	  }
	 
      case ForSt( s, exp1, exp2, exp3, stmt1) => {
		st.insert(s,VarDec(NamedType("INTEGER"),0,0))
      	val i = allocate_variable(new_name("i"),typechecker.typecheck(exp1),fname)
      	val j = allocate_variable(new_name("j"),typechecker.typecheck(exp2),fname)
      	val loop1 = new_name("loop")
        val exit1 = new_name("exit")
        //val body = Seq(stmt1.map(code(_,level,fname)))
      	Seq(List(
      		Move(i, code(exp1,level,fname)),
      		Move(j, code(exp2,level,fname)),
			Label(loop1),
      		CJump(Binop("GT",i,j),exit1),
      		
      		code(stmt1,level,fname), //body
      		Move(i,Binop("PLUS",i,IntValue(1))),
      		CJump(Binop("LEQ",i,j),loop1),
			//Jump(exit1),
      		Label(exit1)))

      }

      // case class WhileSt ( condition: Expr, body: Stmt ) extends Stmt
      case WhileSt(e,st) => {
      	val loop2 = new_name("loop")
      	//val cont = new_name("cont")
        val exit2 = new_name("exit")
        Seq(List(
        	Label(loop2),
        	CJump(Unop("NOT",code(e,level,fname)),exit2),
        	code(st,level,fname),
        	Jump(loop2),
        	Label(exit2)
        	))
      }

	  
	  case ReturnSt() => {
		Return()
	  }
      case SeqSt(st_lst) => {
      	var sq_lst: List[IRstmt] = List()
      	sq_lst = for(st <- st_lst)
	      			yield
	      			{
	      				code(st, level, fname)
	      			}
	    Seq(sq_lst)
      }
	  
	  
	//may need fix
// case class IfSt ( condition: Expr, then_stmt: Stmt, else_stmt: Stmt )
      case IfSt(e, st, est) => {
      	val label_if = new_name("label_if")
      	val label_else = new_name("exit")
      	val exitifelse = new_name("cont")
      	Seq(List(
			CJump(code(e,level,fname),label_else),
      		code(est,level,fname),
      		Jump(exitifelse),
      		Label(label_else),
			code(st,level,fname),
      		
			//Jump(exitifelse),
      		Label(exitifelse)
      		))
      }
//may need fix
	  
	  
      case ReturnValueSt(expp) => {
	  
      	var sq_lst: List[IRstmt] = List() 
      	sq_lst = List(Move(Reg("a0"),
                                                                             Binop("TIMES",
                                                                                   Mem(Binop("PLUS",
                                                                                             Reg("fp"),IntValue(4))),
                                                                                           code(expp,level,fname)  )),Move(Reg("ra"),
                                                                             Mem(Binop("PLUS",
                                                                                       Reg("fp"),
                                                                                       IntValue(-4)))),Move(Reg("sp"),			
	                                                                             Reg("fp")),			
	                                                                        Move(Reg("fp"),			
                                                                            Mem(Reg("fp"))),                                                                   Return())	
      	Seq(sq_lst)
      }
	  
	  
	  //my code
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong statement: " + e)
    }
  }

  /** return the IR code from the Lvalue e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Lvalue, level: Int, fname: String ): IRexp = {
	
    e match {
	
      case Var(s) => access_variable(s,level)

	  
	  //my code
	  case ArrayDeref(l, exp) => {
	  
		//println("hahahah ",l,"mid",exp,"hehe")
		
		l match{
		case Var(_) =>
		
		{
			ESeq(Assert(Binop("AND",
                                                                                   Binop("GEQ",
                                                                                         IntValue(6),
                                                                                         IntValue(0)),
                                                                                   Binop("LT",
                                                                                         IntValue(6),
                                                                                         Mem(Mem(Binop("PLUS",
                                                                                                       Mem(Binop("PLUS",
                                                                                                                 Reg("fp"),
                                                                                                                 IntValue(-8))),
                                                                                                       IntValue(-28))))))),
                                                                      Mem(Binop("PLUS",
                                                                                Mem(Binop("PLUS",
                                                                                          Mem(Binop("PLUS",
                                                                                                    Reg("fp"),
                                                                                                    IntValue(-8))),
                                                                                          IntValue(-28))),
                                                                                Binop("TIMES",
                                                                                      Binop("PLUS",
                                                                                            IntValue(6),
                                                                                            IntValue(1)),
                                                                                      IntValue(4)))))
		
		}
		
		
		
		
		case _ =>
		{
		
      	//code(l,level,fname)
      	//code(exp,level,fname)
		ESeq(Assert(Binop("AND",
                                                        Binop("GEQ",
                                                              IntValue(0),
                                                              IntValue(0)),
                                                        Binop("LT",
                                                              IntValue(0),
                                                              Mem(ESeq(Assert(Binop("AND",
                                                                                    Binop("GEQ",
                                                                                          Mem(Binop("PLUS",	
	                                                                                                                      Reg("fp"),			
                                                                                                                   IntValue(-16))),
                                                                                          IntValue(0)),
                                                                                    Binop("LT",
                                                                                           Mem(Binop("PLUS",	
                                                                                                                     Reg("fp"),			
                                                                                                                      IntValue(-16))),
                                                                                          Mem(Mem(Binop("PLUS",
                                                                                                        Reg("fp"),
                                                                                                        IntValue(-16))))))),
                                                                       Mem(Binop("PLUS",
                                                                                 Mem(Binop("PLUS",
                                                                                           Reg("fp"),
                                                                                           IntValue(-16))),
                                                                                 Binop("TIMES",
                                                                                       Binop("PLUS",
                                                                                             Mem(Binop("PLUS",	
                                                                                                                         Reg("fp"),			
	                                                                                                                         IntValue(-16))),
                                                                                             IntValue(1)),
                                                                                       IntValue(4))))))))),
                                           Mem(Binop("PLUS",
                                                     ESeq(Assert(Binop("AND",
                                                                       Binop("GEQ",
                                                                             Mem(Binop("PLUS",	
	                                                                                                         Reg("fp"),			
	                                                                                                         IntValue(-16))),
                                                                             IntValue(0)),
                                                                       Binop("LT",
                                                                             Mem(Binop("PLUS",	
                                                                                                        Reg("fp"),			
                                                                                                        IntValue(-16))),
                                                                             Mem(Mem(Binop("PLUS",
                                                                                           Reg("fp"),
                                                                                           IntValue(-16))))))),
                                                          Mem(Binop("PLUS",
                                                                    Mem(Binop("PLUS",
                                                                              Reg("fp"),
                                                                              IntValue(-16))),
                                                                    Binop("TIMES",
                                                                          Binop("PLUS",
                                                                                Mem(Binop("PLUS",	
	                                                                                                            Reg("fp"),			
	                                                                                                            IntValue(-16))),
                                                                                IntValue(1)),
                                                                          IntValue(4))))),
                                                     Binop("TIMES",
                                                           Binop("PLUS",
                                                                 IntValue(0),
                                                                 IntValue(1)),
                                                           IntValue(4)))))  
														   
														   }
      }
	  }
	  case RecordDeref(lval, str) => {
      	ESeq(Assert(Binop("NEQ",Mem(Binop("PLUS",Reg("fp"),IntValue(-12))),IntValue(0))),Mem(Binop("PLUS",
                          Mem(Binop("PLUS",Reg("fp"),IntValue(-12))),IntValue(0))))
      }
	  
	  
	  //my code
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong statement: " + e)
    }
  }

  /** return the IR code from the function body (level is the current function nesting level,
   *  f is the name of the current function/procedure) */
  def code ( e: Body, level: Int, f: String ): IRstmt = {
    e match {
      case Body(ds,s) => {
        val defs = Seq(ds.map(code(_,f,level)))
        val body = Seq(s.map(code(_,level,f)))
        val inits = Seq(for ( VarDecls(vds) <- ds;
                              VarDecl(vs,_,u) <- vds;
                              uc = code(u,level,f);
                              v <- vs )
                            yield Move(access_variable(v,level),uc))
        st.lookup(f) match {
          case Some(ProcDec(_,_,fname,_,offset))
            => Seq(List(defs,
                        Label(fname),
                        Move(Mem(Reg("sp")),Reg("fp")),
                        Move(Reg("fp"),Reg("sp")),
                        Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-4))),Reg("ra")),
                        Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),Reg("v0")),
                        Move(Reg("sp"),Binop("PLUS",Reg("sp"),IntValue(offset))),
                        inits,
                        body,
                        Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                        Move(Reg("sp"),Reg("fp")),
                        Move(Reg("fp"),Mem(Reg("fp"))),
                        Return()))
          case _ => throw new Error("Unkown function: "+f)
        }
      }
    }
  }

  /** return the IR code for the declaration block of function fname
   * (level is the current function nesting level) */
  def code ( e: Declaration, fname: String, level: Int ): IRstmt = {
    e match {
      case TypeDecls(tds) => {
        for ( TypeDecl(n,t) <- tds )
              st.insert(n,TypeDec(t))
        Seq(List())
      }
      case VarDecls(vds) => {
        for ( VarDecl(vs,t,u) <- vds; v <- vs )
              if (t == "NoType")
                allocate_variable(v,typechecker.typecheck(u),fname)
              else allocate_variable(v,NamedType(t),fname)
        Seq(List())
      }
      case ProcDecls(pds) => {
        for ( ProcDecl(f,ot,ps,b) <- pds )
            st.insert(f,ProcDec(NamedType(ot),
                                ps.flatMap({
                                    case (vs,t) => vs.map(_ -> NamedType(t))
                                }),new_name(f),level+1,-12))
        Seq( for ( ProcDecl(f,ot,ps,b) <- pds ) yield {
                var i = 4
                st.begin_scope()
                for ( (vs,t) <- ps.reverse; v <- vs.reverse ) {
                      st.insert(v,VarDec(NamedType(t),level+1,i))
                      i += 4
                }
                val res = code(b,level+1,f)
                st.end_scope()
                res
            } )
      }
    }
  }

  /** generate code for the main program */
  def code ( e: ProcDecl ): IRstmt = {
    e match {
      case ProcDecl(f,ot,ps,b) => {
          var i = 4
          st.begin_scope()
          st.insert(f,ProcDec(NamedType(ot),List(),f,1,-12))
          val res = code(b,1,f)
          st.end_scope()
          res
      }
    }
  }

}
