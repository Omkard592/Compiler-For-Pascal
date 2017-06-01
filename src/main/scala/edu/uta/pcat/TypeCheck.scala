/****************************************************************************************************
 *
 * File: TypeCheck.scala
 * The type-checker for PCAT programs
 *
 Omkar Deshmukh
 UTA ID: 1001275806
****************************************************************************************************/

package edu.uta.pcat

import scala.collection.immutable.ListMap


abstract class TypeChecker
{
	var trace_typecheck = false

	/** symbol table to store PCAT declarations */
	var st = new SymbolTable

	/* various types */
	val anyType    = AnyType()
	val noType     = NamedType("NoType")
	val intType    = NamedType("INTEGER")
	val boolType   = NamedType("BOOLEAN")
	val floatType  = NamedType("FLOAT")
	val stringType = NamedType("STRING")

	def expandType ( tp: Type ): Type
	def typecheck ( e: Expr ): Type
	def typecheck ( e: Lvalue ): Type
	def typecheck ( e: Stmt )
	def typecheck ( e: Body, returned: Type )
	def typecheck ( e: ProcDecl )
}


class TypeCheck extends TypeChecker
{

	/** the expected type of the return value from the current function */
	var expected_returned_type: Type = null

	/** If tp is a named type, expand it */
	def expandType ( tp: Type ): Type =
	{
		if (tp.equals(intType) || tp.equals(boolType)
        || tp.equals(floatType) || tp.equals(stringType)
        || tp.equals(anyType) || tp.equals(noType))
			tp
		else tp match
		{
			case NamedType(nm) => st.lookup(nm) match
			{
				case Some(TypeDec(t)) => expandType(t)
				case _ => throw new Error("Undeclared type: "+tp)
			}
			case _ => tp
		}
	}

	/** returns true if the types tp1 and tp2 are equal under name equivalence */
	def typeEquivalence ( tp1: Type, tp2: Type ): Boolean =
	{
		/* AnyType() matches any RecordType(...) */
		if (tp1.equals(tp2))
			true
		else expandType(tp1) match
		{
			case RecordType(_) => tp2.equals(anyType)
			case _ => expandType(tp2) match
			{
				case RecordType(_) => tp1.equals(anyType)
				case _ => false
			}
		}	
	}

	/* Tracing level */
	var level: Int = -1

	def trace[T] ( e: Any, result: => T ): T =
	{
		if (trace_typecheck)
		{
			level += 1
			println(" "*(3*level)+"** "+e)
		}
		val res = result
		if (trace_typecheck)
		{
			print(" "*(3*level))
			if (res == ())
				println("->")
			else
				println("-> "+res)
			level -= 1
		}
		res
	}  

	/** typecheck an expression AST */
	def typecheck ( e: Expr ): Type =
		trace(e,e match
		{
			case BinOpExp(op,l,r) =>
			{
				val ltp = typecheck(l)
				val rtp = typecheck(r)
				
				//if (!typeEquivalence(ltp,rtp))
				//	throw new Error("Incompatible types in binary operation: "+e)
					
				if (op.equals("and") || op.equals("or"))
					boolType
					//if (typeEquivalence(ltp,boolType))
					//	ltp
					//else
					//	throw new Error("AND/OR operation can only be applied to booleans: "+e)
						
				else if (op.equals("eq") || op.equals("neq"))
					if(op.equals("eq") && typeEquivalence(rtp,anyType))
						boolType
					else
						boolType
					
				//else if (!typeEquivalence(ltp,intType) && !typeEquivalence(ltp,floatType))
				//	throw new Error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
					
				else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
					boolType
					  
				//my code
				else if (op.equals("mod") || op.equals("div"))
					if (typeEquivalence(ltp,intType) && typeEquivalence(rtp,intType))
						intType
					else
						throw new Error("MOD/DIV operation can only be applied to integers: "+e)

				else if (op.equals("plus") || op.equals("minus") || op.equals("times"))
					if (typeEquivalence(ltp,intType) && typeEquivalence(rtp,intType))
						intType
					else
						floatType	
						
				else if (op.equals("slash"))
						floatType
				//my code
				
				else
					ltp
			}
	  
			//my code
			case UnOpExp(op,l) =>
			{
				val ltp = typecheck(l)
				if (op.equals("minus"))
					if (typeEquivalence(ltp,intType) || typeEquivalence(ltp,floatType))
						ltp
					else
						throw new Error("MINUS operation can only be applied to integers or float: "+e)
						
				else if (op.equals("not"))
					if (typeEquivalence(ltp,boolType))
						ltp
					else
						throw new Error("NOT operation can only be applied to booleans: "+e)
		
				else
					ltp
			}
	  
			case LvalExp(l) => l match
			{
				case Var("NIL") =>
				{
					st.insert("NIL",VarDec(anyType,0,0))
					typecheck(Var("NIL"))
					anyType
				}
				
				case Var("TRUE") =>
				{
					st.insert("TRUE",VarDec(boolType,0,0))
					typecheck(Var("TRUE"))
					boolType
				}
				
				case Var("FALSE") =>
				{
					st.insert("FALSE",VarDec(boolType,0,0))
					typecheck(Var("FALSE"))
					boolType
				}
				
				case _ =>
				{
					val ltp = typecheck(l)
					ltp
				}
				
			}
	  
			case CallExp(f,args) =>
				st.lookup(f) match
				{
					case Some(ProcDec(otp,params,"",0,0)) =>
					{
						if (params.length != args.length)
							throw new Error("Number of parameters doesn't match number of arguments")
			
						else
							(args.map(typecheck(_)) zip params).map(
							{
								case (atp,(_,ptp)) =>
								if (!typeEquivalence(atp,ptp))
									throw new Error("The type of call argument ("+atp+") does not match the type of the formal parameter: "+ptp)
							})
							otp
					}
					
					case _ =>
						throw new Error("Undefined function: "+f)
				}
			
			case ArrayExp(f,args) => 
			{
				
				val lol = st.lookup(f)
				for(ax <- args)
				{
					ax match
					{
						case (e1,e2) =>
						{
							typecheck(e1)
							typecheck(e2)
						}
					}
				}
				
				val ft = NamedType(f)
				ft
			}				
				
				
			case RecordExp(f,args) => 
			{
			
				for(ax <- args)
				{
					ax match
					{
						case (s,expr) =>
						{
							typecheck(expr)
						}
					}
				}
				
				val ft = NamedType(f)
				ft
			}
				
			case RealConst(r) => 
				NamedType("FLOAT")	
				
			case IntConst(i) => 
				NamedType("INTEGER")	
					
			case StringConst(s) => 
				NamedType("STRING")
					
			//my code

			case _ =>
				throw new Error("Wrong expression: "+e)
		})

	/** typecheck an Lvalue AST */
	def typecheck ( e: Lvalue ): Type =
		trace(e,e match
		{
			case Var(name) =>
				st.lookup(name) match
				{
					case Some(VarDec(t,_,_)) =>
						t
					case Some(_) =>
						throw new Error(name+" is not a variable")
					case None =>
						throw new Error("Undefined variable: "+name)
				}
			
			case ArrayDeref(l,e) =>
			{
				
				val ee = typecheck(e)
				val le = typecheck(l)
				
				if(typeEquivalence(ee,intType) || typeEquivalence(le,anyType))
				{
					var last = NamedType("")
				
					le match 
					{
						case NamedType(x) => 
						{
							val expandl = st.lookup(x)
							expandl match
							{
								case Some(TypeDec(eet)) =>
								{
									val finalt = eet
									finalt match
									{
										case ArrayType(ff) =>
											last = NamedType(ff)
									}
								}
				
								case _ =>
									val dummy = false
							}
							last
						}
					}
				}
				else
					throw new Error("Error in Array Dereferencing")
			}	
			
			case RecordDeref(l,e) =>
			{
				val le = typecheck(l)
				val ee = st.lookup(e)

				if(typeEquivalence(le,anyType))
				{
					ee match
					{
						case Some(TypeDec(eet)) =>
							val finalt = eet
						finalt
					}
				}
				else
					throw new Error("Error in Array Dereferencing")
			}
			
			case _ =>
				throw new Error("Wrong lvalue: "+e)
		})
		
	/** typecheck the body of a function */
	def typecheck ( e: Stmt )
	{
		trace(e,e match
		{
			case AssignSt(d,s) =>
			{
				//if (!typeEquivalence(typecheck(d),typecheck(s)))
				//	throw new Error("Incompatible types in assignment: "+e)
				val td = typecheck(d)
				val ts = typecheck(s)
			}
			
			//my code
			
			case CallSt(s,args) =>
			{
			
				var myl = List(())
				for(a <- args)
				{
					typecheck(a)
					myl = ("") :: myl
				}
				myl = myl.drop(1)
				myl
			}
			
			
			case WriteSt(exp) =>
			{
				exp.foreach(typecheck(_))
			}
			
			case ReadSt(exp) =>
			{
				exp.foreach(typecheck(_))
			}
			
			case SeqSt(exp) =>
			{
				exp.foreach(typecheck(_))
			}
			
			case IfSt(c,t,e) =>
			{
				typecheck(c)
				typecheck(t)
				typecheck(e)
			}
			
			case ReturnSt() =>
			{}
			
			case ExitSt() =>
			{}
			
			case WhileSt(e,b) =>
			{
				typecheck(e)
				typecheck(b)
			}
			
			case LoopSt(exp) =>
			{
				typecheck(exp)
			}
			
			case ForSt(s,e1,e2,e3,b) =>
			{
				st.insert(s,VarDec(intType,0,0))
				typecheck(e1)
				typecheck(e2)
				typecheck(e3)
				typecheck(b)
			}
			
			case ReturnValueSt(exp) =>
			{
				val t = typecheck(exp)
				
			}
			
			//my code
			
			case _ =>
				throw new Error("Wrong statement: "+e)
		})
	}

	/** typecheck the body of a function */
	def typecheck ( e: Body, returned: Type )
	{
		trace(e,e match
		{
			case Body(ds,s) =>
			{
				ds.foreach(typecheck(_))
				expected_returned_type = returned
				s.foreach(typecheck(_))
			}
		})
	}

	/** typecheck a declaration block */
	def typecheck ( e: Declaration )
	{
		trace(e,e match
		{
			case TypeDecls(tds) =>
			for ( TypeDecl(n,t) <- tds )
			{
				st.insert(n,TypeDec(t))
				
				//my code
				t match
				{
					case RecordType(params) => 
					{
						for(p<-params)
						{
							p match
							{
								case (v,t) =>
									st.insert(v,TypeDec(NamedType(t)))
							}
						}
					}
				
					case _ =>
						val t = false
				}
				
				//my code
			}
			
			case VarDecls(vds) =>
			for ( VarDecl(vs,t,u) <- vds; v <- vs )
				if (t == "NoType")
					st.insert(v,VarDec(typecheck(u),0,0))
					
                else if (!typeEquivalence(typecheck(u),NamedType(t)))
					throw new Error("Incompatible types in variable declaration: "+e)
					
                else
					st.insert(v,VarDec(NamedType(t),0,0))
					
			case ProcDecls(pds) =>
			{
				for ( ProcDecl(f,ot,ps,b) <- pds )
					st.insert(f,ProcDec(NamedType(ot), ps.flatMap(
					{
						case (vs,t) => vs.map(_ -> NamedType(t))
                    }),"",0,0))
        
				for ( ProcDecl(f,ot,ps,b) <- pds )
				{
					st.begin_scope()
					for ( (vs,t) <- ps; v <- vs )
						st.insert(v,VarDec(NamedType(t),0,0))
					typecheck(b,NamedType(ot))
					st.end_scope()
				}
			}
		})
	}

	/** typecheck the main program */
	def typecheck ( e: ProcDecl )
	{
		try
		{
			trace(e,e match 
			{
				case ProcDecl(f,ot,ps,b) =>
				{
					st.begin_scope()
					typecheck(b,NamedType(ot))
					st.end_scope()
				}
			})
		}
		catch
		{
			case e: Error => println("*** Type checking error: " + e)
			sys.exit(-1)
		}
	}
}