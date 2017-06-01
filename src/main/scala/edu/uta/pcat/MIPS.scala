/****************************************************************************************************
 *
 * File: MIPS.scala
 * Generation of MIPS code from IR code
 *
 ****************************************************************************************************/

package edu.uta.pcat

/** representation of a MIPS register */
case class Register ( val reg: String ) {
    override def toString (): String = reg
}


/** a pool of available registers */
class RegisterPool {

  val all_registers
        = List( "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9",
                "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7" )

  var available_registers = all_registers.map(Register(_))

  /** is register reg temporary? */
  def is_temporary ( reg: Register ): Boolean =
    reg match {
      case Register(n) => all_registers.contains(n)
    }

  /** return the next available temporary register */
  def get (): Register =
    available_registers match {
      case reg::rs => {
        available_registers = rs
        reg
      }
      case _ => throw new Error("*** Run out of registers")
    }

  /** recycle (put back into the register pool) the register reg (if is temporary) */
  def recycle ( reg: Register ) {
    if (available_registers.contains(reg))
      throw new Error("*** Register has already been recycled: "+reg)
    if (is_temporary(reg))
      available_registers = reg::available_registers
  }

  /** return the list of all temporary registers currently in use */
  def used (): List[Register] = {
    for ( reg <- all_registers
          if (!available_registers.contains(Register(reg))) )
      yield Register(reg)
  }
}


abstract class MipsGenerator {
  def clear ()
  def emit ( e: IRstmt )
}


class Mips extends MipsGenerator {

  var assert_count = 1

  /** emit a MIPS label */
  def mips_label ( s: String ) {
    PCAT.out.println(s + ":")
  }

  /** emit MIPS code with no operands */
  def mips ( op: String ) {
    PCAT.out.println("        " + op)
  }

  /** emit MIPS code with operands */
  def mips ( op: String, args: String ) {
    PCAT.out.print("        " + op)
    for ( i <- op.length to 10)
        PCAT.out.print(" ")
    PCAT.out.println(args)
  }

  /** a pool of temporary registers */
  var rpool = new RegisterPool

  /** clear the register pool */
  def clear () {
    rpool = new RegisterPool
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  /** generate MIPS code from the IR expression e and return the register that will hold the result */
  def emit ( e: IRexp ): Register = {
    e match {

	
		
      case Mem(Binop("PLUS",Reg(r),IntValue(n))) => {
		val reg1 = Register(""+n +"("+emit(Reg(r))+")")
        reg1
      }


	  
	  
	  case Binop(opr, op1, op2) => {
			op1 match {
				case Mem(x) => {
					val reg = rpool.get()
					val reg1 = emit(Mem(x))
					val str1 = reg1.toString()
					val len1 = str1.length()

					len1 match {
						case 3 => {
							mips("lw",reg+ ", (" + reg1+")")
						}
						case _ => {
							mips("lw",reg+ ", " + reg1)
						}
					}
					
					val reg4 = rpool.get()
					op2 match {
						case IntValue(n) => {
							mips("li",reg4 + ", "+emit(op2))
						}
						case _ => {
							val regop2 = emit(op2)
							
							val str = regop2.toString()
							val len = str.length()

							len match {
								case 3 => {
									mips("lw",reg4 + ", ("+regop2+")")
								}
								case _ => {
									mips("lw",reg4 + ", "+regop2)
								}
							}
							
						}
					}
					
					
					opr match {
					case "PLUS" => {
						mips("addu",reg+", "+reg+", "+reg4)
					}
					case "TIMES" => {
						mips("mul",reg+", "+reg+", "+reg4)
					}
					case "MINUS" => {
						mips("subu",reg+", "+reg+", "+reg4)
					}
					case "GEQ" => {
						//mips("GEQ Binop")
						mips("sge",reg+", "+reg+", "+reg4)
					}
					case "AND" => {
							//mips("AND Binop")
						}
					case "LT" => {
							//mips("LT Binop")
							mips("slt",reg+", "+reg+", "+reg4)
						}
					}
					rpool.recycle(reg4)
					//rpool.recycle(reg)
					reg
				}
				
				
				case _ => {
				
					var oprtype = ""
					opr match {
						case "AND" => {
							//mips("AND Binop normal")
							oprtype = "AND Binop normal"
						}
						case "PLUS" => {
							//mips(opr+", "+op1+", "+op2)
							//mips("lw",reg1+", "+emit(op2))
							oprtype = "addu"
							//mips("PLUS Binop normal")
						}
						case "GEQ" => {
							//mips("GEQ Binop normal")
							//mips("sge",reg+", "+reg+", "+reg1)
							oprtype = "sge"
						}
						case "LT" => {
							//mips("LT Binop normal")
							//mips("slt",reg+", "+reg+", "+reg1)
							oprtype = "slt"
						}
						case "TIMES" => {
							oprtype = "mul"
						}
					}
					op1 match {
						case IntValue(n) => {
							val reg1 = rpool.get()
							mips("li",reg1+", "+emit(op1))
							val reg2 = rpool.get()
							mips("lw",reg2+", "+emit(op2))
							mips(oprtype,reg1+", "+reg1+", "+reg2)
							rpool.recycle(reg2)
							rpool.recycle(reg1)
							reg1
						}
						case _ => {
							val reg1 = rpool.get()
							mips("lw",reg1+", ("+emit(op1)+")")
							val reg2 = rpool.get()
							mips("li",reg2 + ", "+emit(op2))
							mips(oprtype,reg1+", "+reg1+", "+reg2)
							rpool.recycle(reg2)
							rpool.recycle(reg1)
							reg1
						}
					}					
				}
			}
	  }
	  
	  
	  
	  
	  case Reg(x) => {
		val reg = Register("$"+x)
		reg
		}
		
		
	  case Mem(regx) => {
		val reg = Register(""+emit(regx)+"")
		reg
	  }
	  
	  
      case Binop("AND",x,y) => {
        val label = new_label()
        val left = emit(x)
        val reg = left
        mips("beq",left+", 0, "+label)
        val right = emit(y)
        mips("move",left+", "+right)
        mips_label(label)
        rpool.recycle(right)
        reg
      }
	  
	  
	  case Call(f,sl,args) => {
        val used_regs = rpool.used()
        val size = (used_regs.length+args.length)*4
        /* allocate space for used temporary registers */
        if (size > 0)
            mips("subu","$sp, $sp, "+size)
        /* push the used temporary registers */
        var i = size
        for (r <- used_regs) {
            mips("sw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* push arguments */
        i = args.length*4
        for (a <- args) {
          val reg = emit(a)
          mips("sw",reg + ", " + i + "($sp)")
          rpool.recycle(reg)
          i -= 4
        }
        /* set $v0 to be the static link */
        val sreg = emit(sl)
        mips("move","$v0, " + sreg)
        rpool.recycle(sreg)
        mips("jal",f)
        i = size
        /* pop the used temporary registers */
        for (r <- used_regs) {
            mips("lw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* deallocate stack from args and used temporary registers */
        if (size > 0)
            mips("addu","$sp, $sp, "+size)
        val res = rpool.get()
        mips("move",res + ", $a0")
        /* You shouldn't just return $a0 */
        res
      }
	  
      /* PUT YOUR CODE HERE */
		
		case IntValue(n) => {
		val reg = Register(""+n+"")
		reg
		}
		
		
		
	  
	  
      case _ => throw new Error("Unknown IR: "+e)
    }
  }
  
  
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  
  

  /** generate MIPS code from the IR statement e */
  def emit ( e: IRstmt ) {
    e match {
		case Move(Reg(x),y) => {
			y match {
				case Reg(r) => {
					mips("move",emit(Reg(x))+", "+emit(y))
				}
				
				case IntValue(n) => {
					mips("li",emit(Reg(x)) + ", " + emit(y))
				}
				
				case Binop(opr, op1, op2) => {
					val reg1 = rpool.get()
					mips("li",reg1 + ", " + emit(op2))
					val reg2 = rpool.get()
					opr match {
						case "PLUS" => {
							mips("addu",reg2+", "+emit(Reg(x))+", "+reg1)
						}
						case "TIMES" => {
							mips("mul",reg2+", "+emit(Reg(x))+", "+reg1)
						}
						case _ => {
							mips("WRONG BINOP OPR HERE Binop")
						}
					}
					mips("move",emit(Reg(x))+", "+ reg2)
					rpool.recycle(reg2)
					rpool.recycle(reg1)
				}
				
				case Mem(m) => {
					val reg = emit(Mem(m))
					m match {
						case Reg(fp) => {
							mips("lw",emit(Reg(x)) + ", (" + reg+")")
						}
						case Binop(opr, op1, op2) => {
							opr match {
								case "PLUS" => {
									mips("lw",emit(Reg(x)) + ", " + reg)
								}
								case _ => {
									mips("WRONG BINOP OPR HERE Mem(m)")
								}
							}
							
						}
					}		
				}				
			}
		}
		
		case Move(Mem(x),y) => {
			x match {
				case Binop(opr, op1, op2) => {
					val reg = emit(Mem(x))
					y match {
						case Reg(r) => {
							mips("sw",emit(Reg(r))+", "+reg)
						}
						case IntValue(n) => {
							val reg1 = rpool.get()
							mips("li",reg1 + ", " + n)
							val str = reg.toString()
							val len = str.length()

							len match {
								case 3 => {
									mips("sw",reg1+", ("+reg+")")
								}
								case _ => {
									mips("sw",reg1+", "+reg)
								}
							}
							rpool.recycle(reg1)
						}
						
						case Allocate(a) => {
							
							a match {
								case Binop(opr, op1, op2) => {
									val regal = emit(Binop(opr, op1, op2))
									//mips("Allocate binop")
								}
								
								case IntValue(n2) => {
									//mips("Allocate other")
									val rega = rpool.get()
									mips("li",rega + ", "+emit(a))
									rpool.recycle(rega)
								}
							}	
								
							
							val rega = rpool.get()
							val reg1 = rpool.get()
							mips("li",reg1 + ", 4")
							
							mips("mul",rega+", "+rega+", "+reg1)
							mips("move",reg1+", $gp")
							mips("addu","$gp, $gp, "+rega)
							mips("sw",reg1+ ", "+reg)
							rpool.recycle(reg1)
							rpool.recycle(rega)			
						}
												
						case Mem(m) => {
							val reg1 = emit(Mem(m))
							val reg2 = rpool.get()
							mips("lw",reg2+ ", " + reg1)
							mips("sw",reg2+ ", "+reg)
							rpool.recycle(reg2)
						}
						
						case Binop(opr, op1, op2) => {
							val regb = emit(y)
							mips("sw",regb+ ", "+reg)
						}
						
						case Unop(opr, op1) => {
							mips("UNOP LOWER")
					  }
	  
						case Call(a,b,c) => {
							val creg = emit(Call(a,b,c))
							mips("sw",creg+ ", "+reg)
						}
						
					}
				}
				
				case Reg(r) => {
					mips("sw",emit(y)+", ("+emit(Reg(r))+")")
				}
				
				case _ => {
					val rege = emit(x)
					val reg = rpool.get()
					mips("lw",reg+ ", " + rege)
					y match {
						case IntValue(n) => {
							
							val reg1 = rpool.get()
							mips("li",reg1 + ", " + n)
							mips("sw",reg1+", ("+reg+")")
							rpool.recycle(reg1)
						}
						
						case _ => {
							val reg1 = emit(y)
							mips("sw",reg1+", ("+reg+")")
						}
					}
					rpool.recycle(reg)
				}
				
			}
			
		}
		
		case Assert(Binop(opr,op1,op2)) => {
			op1 match {
				case Mem(x) => {
					val reg = rpool.get()
					val reg1 = emit(Mem(x))
					mips("lw",reg+ ", " + reg1)
					val reg4 = rpool.get()
					mips("li",reg4 + ", "+emit(op2))
					mips("sne",reg+", "+reg+", "+reg4)  
					mips_label("ASSERT_"+(assert_count))
					mips("li","$v0, "+(assert_count))
					assert_count+=1
					opr match {
						case "NEQ" => {
						mips("beq",reg+", 0, Assertion_failure")
						}
					}
					rpool.recycle(reg4)
					rpool.recycle(reg)
				}
				case _ => {
					val regas = emit(op1)
					val label = new_label()
					mips("beq",regas+", 0, "+label)
					//mips("New assert op1")
					val regab = emit(op2)
					mips("move",regas+", "+regab)
					mips_label(label)
					mips_label("ASSERT_"+(assert_count))
					mips("li","$v0, "+(assert_count))
					assert_count+=1
					mips("beq",regas+", 0, Assertion_failure")
				}
			}
		}
	  
	  case CallP(f,sl,args) => {
        val used_regs = rpool.used()
        val size = (used_regs.length+args.length)*4
        /* allocate space for used temporary registers */
        if (size > 0)
            mips("subu","$sp, $sp, "+size)
        /* push the used temporary registers */
        var i = size
        for (r <- used_regs) {
            mips("sw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* push arguments */
        i = args.length*4
        for (a <- args) {
			val reg = emit(a)
			a match {
				case IntValue(n) => {
					val rp = rpool.get()
					mips("li",rp+", "+reg)
					rpool.recycle(rp)
					mips("sw",rp + ", " + i + "($sp)")
				}
				
				case Mem(Binop("PLUS",Reg(fp),IntValue(n))) => {
					val rp = rpool.get()
					mips("lw",rp+", "+reg)
					mips("sw",rp + ", " + i + "($sp)")
					rpool.recycle(rp)
					
				}
				
				case _ => {
					val rp = rpool.get()
					mips("sw",reg + ", " + i + "($sp)")
					rpool.recycle(rp)
				}
			}
          rpool.recycle(reg)
          
          i -= 4
        }
        /* set $v0 to be the static link */
        val sreg = emit(sl)
		sl match {
			case Reg(x) => {
				mips("move","$v0, " + sreg)
			}
			case _ => {
				val rp = rpool.get()
				mips("lw",rp+", "+sreg)
				mips("move","$v0, " + rp)
				rpool.recycle(rp)
			}
		}
        rpool.recycle(sreg)
        mips("jal",f)
        i = size
        /* pop the used temporary registers */
        for (r <- used_regs) {
            mips("lw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* deallocate stack from args and used temporary registers */
        if (size > 0)
            mips("addu","$sp, $sp, "+size)
      }
	  
	  case SystemCall("WRITE_STRING", StringValue(str)) => {
		  str match {
			  case "\\n" => {
				mips("li","$v0, 4")
				mips("la","$a0, ENDL_")
				mips("syscall")
			  }
		  
			  case _ => {
				mips(".data")
				mips(".align","2")
				val label = new_label()
				mips_label(label)
				mips(".asciiz","\""+str+"\"")
				mips(".text")
				val reg1 = rpool.get()
				mips("la",reg1+", "+label)
				mips("move","$a0, "+ reg1)
				mips("li","$v0" + ", 4")
				mips("syscall")
				rpool.recycle(reg1)
			  }
		  }
	    
	  }
	  
	  
	  case SystemCall("WRITE_INT", Mem(x)) => {
			x match {
				case Binop("PLUS",Mem(Binop("PLUS", Reg(fp), IntValue(n1))),IntValue(n2)) => {
					mips("lw","$t1, "+emit(Mem(Binop("PLUS", Reg(fp), IntValue(n1)))))
					mips("lw","$t0, "+emit(IntValue(n2))+"($t1)")
					val reg = rpool.get()
					mips("move","$a0, "+ reg)
					mips("li","$v0" + ", 1")
					mips("syscall")
					rpool.recycle(reg)
				}
				
				case _ => {
				
				  val reg = rpool.get()
				  val reg1 = emit(Mem(x))
				  mips("lw",reg+ ", " + reg1)
				  mips("move","$a0, "+ reg)
				  mips("li","$v0" + ", 1")
				  mips("syscall")
				  rpool.recycle(reg)
				}
			} 
	  }

	  case SystemCall("WRITE_INT", Binop(opr,op1,op2)) => {
				val reg = rpool.get()
				val reg1 = emit(Binop(opr,op1,op2))
				mips("move","$a0, "+ reg)
				mips("li","$v0" + ", 1")
				mips("syscall")
				rpool.recycle(reg)
	  }
	  
	  case SystemCall("WRITE_INT", Call(x,a,b)) => {
			val rc = emit(Call(x,a,b))
			mips("move","$a0, "+ rc)
			mips("li","$v0" + ", 1")
			mips("syscall")
			rpool.recycle(rc)
	  }
	  
	  
	  case SystemCall("WRITE_INT", Binop("PLUS", IntValue(n1), Binop("TIMES", Mem(y), IntValue(n2)))) => {
				val reg = rpool.get()
				mips("li",reg + ", 1")
				val reg2 = emit(Binop("TIMES", Mem(y), IntValue(n2)))
				mips("addu",reg+", "+reg+", "+reg2)
				mips("move","$a0, "+ reg)
				mips("li","$v0" + ", 1")
				mips("syscall")
				rpool.recycle(reg)
	  }
	  
	  case SystemCall("READ_INT", Mem(x)) => {
		  
			  mips("li","$v0" + ", 5")
			  mips("syscall")
			  val reg = emit(Mem(x))
			  mips("sw","$v0, ("+ reg+")")
	  }
	  
	  
	  case CJump(Unop(op,e),jlabel) => {
			//mips("UNOPS CJUMP")
			val regu = emit(e)
			mips("seq",regu+", "+regu+", 0")
			mips("beq",regu+", 1, "+jlabel)
	  }
	  
	  case CJump(Binop(opr,op1,op2),jlabel) => {
		
		val rega2 = emit(op1)
		val str1 = rega2.toString()
		val len1 = str1.length()

		val rega1 = rpool.get()
		len1 match {
			case 3 => {
				mips("lw",rega1+ ", (" + rega2+")")
			}
			case _ => {
				mips("lw",rega1+ ", " + rega2)
			}
		}
		
		
		val regb2 = emit(op2)
		val regb1 = rpool.get()
		op2 match {
			case IntValue(in) => {
				mips("li",regb1+ ", " + regb2)
			}
			case _ => {
				val str = regb2.toString()
				val len = str.length()

				len match {
					case 3 => {
						mips("lw",regb1+ ", (" + regb2+")")
					}
					case _ => {
						mips("lw",regb1+ ", " + regb2)
					}
				}
			}
		}

		opr match {
		 case "GT" => {
			mips("sgt",rega1+", "+rega1+", "+regb1)
		 }
		 
		 case "LT" => {
			mips("slt",rega1+", "+rega1+", "+regb1)
		 }
		 
		 case "NEQ" => {
			mips("sne",rega1+", "+rega1+", "+regb1)
		 }
		 
		 case "GEQ" => {
			mips("sge",rega1+", "+rega1+", "+regb1)
		 }
		 
		 case "LEQ" => {
			mips("sle",rega1+", "+rega1+", "+regb1)
		 }
		 
		 case "EQ" => {
			mips("seq",rega1+", "+rega1+", "+regb1)
		 }
		 case "AND" => {
			//mips("CJUMP AND")
		 }
		}
		
		mips("beq",rega1+", 1, "+jlabel)
		
		rpool.recycle(regb1)
		rpool.recycle(rega1)
	  }
	  
	  
	  
	  case Label(x) => {
		x match {
			case "main" => {
				mips(".globl","main")
				mips(".data")
				mips_label("AF_")
				mips(".asciiz","\"\\n*** Assertion Failure at address: ASSERT_\"")
				mips_label("ENDL_")
				mips(".asciiz","\"\\n\"")
				mips(".text")
				mips_label("Assertion_failure")
				val reg1 = rpool.get()
				mips("move",reg1+", $v0")
				mips("li","$v0, 4")
				mips("la","$a0, AF_")
				mips("syscall")
				mips("move","$a0, "+ reg1)
				mips("li","$v0, 1")
				mips("syscall")
				mips("li","$v0, 4")
				mips("la","$a0, ENDL_")
				mips("syscall")
				mips("li","$v0, 10")
				mips("syscall")
				mips_label("main")
				rpool.recycle(reg1)
			}
			case _ => {
				mips_label(x)
			}
		}
	  }
	  
	  case Jump(jlabel) => {
		mips("j",jlabel)
	  }
	  
	  case Return() => {
		mips("jr","$ra")
	  }
	  
      case _ => throw new Error("Unknown IR: "+e)
    }
  }
}
