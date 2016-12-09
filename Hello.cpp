#define debug_stride_pass false
//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//
#include "llvm/IR/DebugInfo.h"
#include<iostream>
#include<sstream>
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LICM.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/Loads.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopPassManager.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/PredIteratorCache.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include <algorithm>


#include <vector>
#include <deque>
#include <set>
#include <map>
#include <algorithm>
#include <ostream>
#include <fstream>
#include <iostream>
using namespace llvm;

#define DEBUG_TYPE "hello"

//STATISTIC(HelloCounter, "Counts number of functions greeted");

namespace {
    StringRef XblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.x" ) ;
    StringRef YblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.y" ) ;
    StringRef ZblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.z" ) ;
    StringRef xthreadDim("llvm.nvvm.read.ptx.sreg.ntid.x");
    StringRef ythreadDim("llvm.nvvm.read.ptx.sreg.ntid.y");
    StringRef xthreadin("llvm.nvvm.read.ptx.sreg.tid.x");
    StringRef ythreadin("llvm.nvvm.read.ptx.sreg.tid.y");
    StringRef zthreadin("llvm.nvvm.read.ptx.sreg.tid.z");
    // Insert Block Stride Computation Instruction 
    struct ComputeBlockStride : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        Function *wrapper_printfFunction;
        Module *thisMod;
        const DataLayout *dlayout ;
        bool cannot_compute, got_a_phi_node;
        bool got_block_index_instr, computed_stride_found;
        char  block_stride_X;
        Value *XblockDim;
        Value *YblockDim;
        Function *thisFunc;
        std::set<Instruction*> alreadyDoneInstr_set;
        std::set<std::string> function_already_done_set;
        //        std::string print_msg;
        GlobalVariable *printfStringMod;
    Value* XblockIndexV;
    Value* YblockIndexV;
    Value* XthreadIndexV;
    Value* YthreadIndexV;
        std::set<Value* > visit_done_set;
        ComputeBlockStride() : FunctionPass(ID) { 
            if (debug_stride_pass) errs()<<"\n registered on constructor";
            //print_msg="Debug Stride = %d";
            XblockIndexV = nullptr;
            YblockIndexV = nullptr;
            XthreadIndexV = nullptr;
            YthreadIndexV = nullptr;
        }


        bool runOnFunction(Function &Func) override {
            thisFunc = &Func;
            if (function_already_done_set.find(std::string(Func.getName())) != function_already_done_set.end()) return false;
            function_already_done_set.insert(std::string(Func.getName()));
            bool written_once=false;
            isFuncArg_visited_set.clear();
            //Instruction *firstInstr = &*inst_begin(Func);
            Instruction *gep_last;
            thisMod = (*inst_begin(Func)).getModule() ;
            dlayout = &(Func.getParent()->getDataLayout());
            got_block_index_instr = false;
            computed_stride_found=false;
            XblockDim=nullptr;
            YblockDim=nullptr;
            // func is a pointer to a Function instance
            //getPrintfFunction((*inst_begin(Func)).getModule() ) ;
            for (Function::iterator basicBlockIterator = Func.begin(), basicBlockEnd = Func.end(); basicBlockIterator != basicBlockEnd; ++basicBlockIterator) {
                //errs() << "Basic block (name=" << basicBlockIterator->getName() << ") has "<< basicBlockIterator->size() << " instructions.\n";
                for (BasicBlock::iterator instructionIterator = basicBlockIterator->begin(), instructionEnd =
                        basicBlockIterator->end(); instructionIterator != instructionEnd;++instructionIterator) {
                    if (debug_stride_pass) errs() << *instructionIterator << "\n";
                    if (!got_block_index_instr ) set_if_block_index_instr(cast<Instruction>( instructionIterator));
                    if (  CallInst *callerI = dyn_cast<CallInst>(instructionIterator)){
                        Function * calledFunc = callerI->getCalledFunction();
                        if (!called.hasName()) continue;
                        StringRef functionName = calledFunc->getName();
                        if (XblockIndexV == nullptr && functionName.equals(XblockIdxString )  )
                            XblockIndexV = callerI;
                        if (XthreadIndexV == nullptr && functionName.equals(xthreadin )  )
                            XthreadIndexV = callerI;
                    }
                        if (got_block_index_instr) {
                            if (!written_once) {
                                errs() << "\nRunning Pass on Function::";
                                errs().write_escaped(Func.getName()) << '\n';
                                written_once=true;
                            }
                            if (GetElementPtrInst *gep= dyn_cast<GetElementPtrInst>(instructionIterator)) {
                                IRBuilder<> l_builder(gep);
                                analyzeGEP(gep, l_builder );
                                gep_last = gep;
            //errs()<<"\n Mod func::"<<Func;
            //return true ;
                            }
                        }
                    }
            }
            if (0) //TODO REMOVE THIS
                if (computed_stride_found ){
                    IRBuilder<> builder(gep_last );
                    if (XblockDim) {
                        std::string print_msg("\n XDIM=%d");
                        instrument_printf_stride(print_msg, XblockDim, builder);
                    }
                    if (YblockDim){
                        std::string print_msg("\n YDIM=%d");
                        instrument_printf_stride(print_msg, YblockDim, builder);
                    }
                    for (Function::arg_iterator ArgIt = Func.arg_begin(), End = Func.arg_end();ArgIt != End; ++ArgIt) {
                        Value *A = &*ArgIt;
                        if (!(A->getType()->isIntegerTy())) continue;
                        std::ostringstream s;
                        s<<"\n Argument ::"<<std::string(A->getName())<<"=%d ";
                        std::string print_msg = s.str();
                        instrument_printf_stride(print_msg, A, builder);
                    }

                    return true;
                }
            //errs()<<"\n Mod func::"<<Func;
            return true ;
        }
        std::set<const Instruction*> isFuncArg_visited_set;
        bool isFuncArg(const Instruction *instr ){
            if (isFuncArg_visited_set.find(instr) != isFuncArg_visited_set.end() ) return false;
            isFuncArg_visited_set.insert(instr);
            for (int i=0, n= instr->getNumOperands();i<n;i++ ){
                Value *op = instr->getOperand(i);
                //	errs()<<"\n op::"<<*op<<(isa<Argument>(op ));
                if (isa<Argument>(op )) return true; 
                if (isa<Instruction>(op )) 
                    if (isFuncArg(dyn_cast<Instruction>(op) ) )return true; 
            }
            return false;
        }

        void analyzeGEP( GetElementPtrInst *gep,IRBuilder<> &builder ) {
            Value *mem = gep->getPointerOperand();
            if (debug_stride_pass) errs()<<"\n Working with gep::"<<*gep;
            if  (const Instruction *i= dyn_cast<Instruction>(mem)){
                if (isFuncArg(i ) )	 {
                    //errs()<<"\n got an argument"<<*mem;
                }else {
                    //errs()<<"\n Not an argument"<<*mem;
                    return;
                }
            }
            /*if  (const Argument *arg = dyn_cast<Argument>(mem)){
              errs()<<"\n got an argument"<<*mem;
              } else {
              errs()<<"\n Not an argument"<<*mem;
              return;
              }*/
            Value *index0 = gep->getOperand(1);
            int memDim = (gep->getNumOperands()-1);
            if (Instruction* indexInstr = dyn_cast<Instruction>(index0 ) ) {
                if (alreadyDoneInstr_set.find(gep) != alreadyDoneInstr_set.end()) return;
                DILocation *loc = gep->getDebugLoc();
                unsigned line_num = 0 ;
                std::string filename_dbg;
                if (loc) line_num = loc->getLine();
                if (loc) filename_dbg = loc->getFilename().str();
                errs()<<"\nAnalyzing memory:: "<<*mem<<" for file line: "<<filename_dbg<<":"<<line_num ;//<<" with dimensions::"<< memDim ;
                for (block_stride_X=1;block_stride_X<=2;block_stride_X++) {
                    visit_done_set.clear();
                    Value *computedStride = nullptr; 
                    cannot_compute= false;
                    got_a_phi_node = false;
                    bool is_index = get_block_stride_instr(indexInstr, builder, computedStride );
                    if ( !cannot_compute && computedStride != nullptr ) {
                        errs()<<"\t block stride in "<<(block_stride_X==1?"X":"Y") ;
                        if (is_index ){
                            errs()<< "::"<<*computedStride;
                            std::ostringstream s;
                            s<<"\n Block Stride in "<<(block_stride_X==1?"X":"Y")<<" dim for ::";
                            s<<std::string(mem->getName());
                            s<<" reference at line "<<line_num<<" is %d";
                            uint64_t mytypeSize = dlayout->getTypeStoreSize(computedStride->getType());
                            s<<" size="<<mytypeSize;
                            std::string print_msg = s.str();
                            //Value *blockStrideSize =  builder.CreateBinOp(Instruction::Mul, mytypeSize, computedStride,"final_stride_compute_mul");
                            //insert_block_index_call(builder, gep);
                            instrument_printf_stride(print_msg, computedStride, builder, true);
                            computed_stride_found=true;
                            break;
                        } else 
                            errs()<<" is 0";
                    }
                    if (cannot_compute) {
                        errs()<<"\t Could Not Compute Block Stride";
                        break;
                    }
                }
                alreadyDoneInstr_set.insert(gep);
            }
        }
        void insert_block_index_call(IRBuilder<> &builder, Instruction *beforeInstr ) {
            //Function *xblockIndexFunc =dyn_cast<Function>( thisMod->getOrInsertFunction("llvm.nvvm.read.ptx.sreg.ctaid.x",
            //            FunctionType::get(IntegerType::getInt32Ty(thisMod->getContext()),
            //                Type::getVoidTy(thisMod->getContext()) ,false) 
            //            ) );
            //Function *yblockIndexFunc =dyn_cast<Function>( thisMod->getOrInsertFunction("llvm.nvvm.read.ptx.sreg.ctaid.y",
            //            FunctionType::get(IntegerType::getInt32Ty(thisMod->getContext()),
            //                Type::getVoidTy(thisMod->getContext()) ,false) 
            //            ) );
            //Function *xthreadIndexFunc =dyn_cast<Function>( thisMod->getOrInsertFunction("llvm.nvvm.read.ptx.sreg.tid.x",
            //            FunctionType::get(IntegerType::getInt32Ty(thisMod->getContext()),
            //                Type::getVoidTy(thisMod->getContext()) ,false) 
            //            ) );
            if (XblockIndexV != nullptr) {
            Value * cond = builder.CreateICmpEQ(XblockIndexV,llvm::ConstantInt::get(builder.getInt32Ty(),0));
            BasicBlock *trueBlock1 = BasicBlock::Create( thisMod->getContext(), "print_true",thisFunc);
            BasicBlock *falseBlock1 = BasicBlock::Create( thisMod->getContext(), "print_fals",thisFunc);
            BranchInst *branch_index = builder.CreateCondBr (  cond,trueBlock1,beforeInstr->getParent());// falseBlock1);
            //BranchInst *branch_index = BranchInst::Create(trueBlock1,beforeInstr->getParent(),cond,  beforeInstr);
            //builder.Insert(branch_index);
            //builder.SetInsertPoint(falseBlock1);
            //Instruction *falselastBr = builder.CreateBr(beforeInstr->getParent());
            builder.SetInsertPoint(trueBlock1);
            Instruction *lastBr = builder.CreateBr(beforeInstr->getParent());
            builder.SetInsertPoint(lastBr);
                errs()<<"\n func::"<<*XblockIndexV;
                errs()<<"\n cond::"<<*cond;
                errs()<<"\n branch ::"<< *branch_index  ;
                errs()<<"\n";
                //errs()<<"\n inserted add::"<<*(builder.CreateAdd( ConstantInt::get(builder.getInt32Ty(),0),
                //ConstantInt::get(builder.getInt32Ty(),0) ));
                //builder.SetInsertPoint(trueBlock1);
                //errs()<<"\n falsebasic block::"<<*falseBlock1;
                errs()<<"\n true       block::"<<*trueBlock1;
            }
            //BasicBlock *trueBlock2 = BasicBlock::Create( thisMod->getContext(), "print_true",thisFunc);
            //BasicBlock *falseBlock2 = BasicBlock::Create( thisMod->getContext(), "print_true",thisFunc);
            //Value* threadIndexV = builder.CreateCall(xthreadIndexFunc );
            //builder.CreateCondBr(builder.CreateICmpEQ(threadIndexV,
            //            llvm::ConstantInt::get(builder.getInt32Ty(),
            //                0)),
            //        trueBlock2, falseBlock2);
            //builder.SetInsertPoint(trueBlock2);
        }
        void instrument_printf_stride(std::string print_msg,Value *computedStride,IRBuilder<> &builder ,bool
                compile_prinit=false ) {
            if (compile_prinit) print_instr(computedStride);
            //return; //TODO REMOVE THIS
            std::vector<Value *> ArgsV;
            GlobalVariable *string_printf = getStringRef(print_msg );
            Constant* zero_i64 = Constant::getNullValue(IntegerType::getInt64Ty(thisMod->getContext()));
            ArrayRef< Value * > indices = {zero_i64,zero_i64};
            PointerType *pty = dyn_cast<PointerType>(string_printf->getType());
            GetElementPtrInst *gep_printf_string = GetElementPtrInst::Create( pty->getElementType(), string_printf,indices );
            if (debug_stride_pass) errs()<<"printf string load:: " <<*gep_printf_string;
            Value *printf_str_gep = builder.Insert(gep_printf_string,"tmp_blockstride_compute" );
            ////ArgsV.push_back( geti8StrVal(*thisMod));
            //errs()<<"\n param type::"<<*computedStride->getType()<<"function wrapper::"<<*wrapper_printfFunction;
            Type *struct_ty = StructType::get(computedStride->getType(),nullptr );
            //Type *struct_ty = StructType::get(IntegerType::getInt32Ty(thisMod->getContext()),nullptr );
            if (debug_stride_pass) errs()<<"\n struct type:: "<<*struct_ty;
            Value * tmp_print_mem = builder.CreateAlloca(struct_ty ,nullptr, "tmp_stride_comp" );
            if (debug_stride_pass) errs()<<"\n alloca instr::"<<*tmp_print_mem<<"\n";

            Constant* zero_i32 = Constant::getNullValue(IntegerType::getInt32Ty(thisMod->getContext()));
            ArrayRef< Value * > indices2 = {zero_i64,zero_i32};
            //if (debug_stride_pass) errs()<<"\n Creating gep with pointer::"<<*tmp_print_mem<< "\n and indiex::"<<*indices[0]<<" and ::"<<*indices[1]<<"\n";
            //if (debug_stride_pass) errs()<<"\n pointer type::"<<*cast<PointerType>(tmp_print_mem->getType()->getScalarType())->getElementType()<<"\n"; 
            GetElementPtrInst *gepInstr = GetElementPtrInst::Create( struct_ty, tmp_print_mem,indices2 );
            Value *print_args_pointer = builder.Insert(gepInstr,"tmp_blockstride_compute" );// 	 builder.CreateGEP(tmp_print_mem,Constant::getNullValue(IntegerType::getInt32Ty(thisMod->getContext())));//indices);
            if (debug_stride_pass) errs()<<"\n printargspointer::"<<*print_args_pointer<<"\n ";
            Value *stored_arg = builder.CreateStore(computedStride,print_args_pointer );
            if (debug_stride_pass) errs()<<"store::"<<*stored_arg;
            Value *bitcast_arg = builder.CreateBitCast(tmp_print_mem,PointerType::get(IntegerType::getInt8Ty(thisMod->getContext()),0 ));
            ArgsV.push_back(printf_str_gep);  
            ArgsV.push_back(bitcast_arg);
            //if (debug_stride_pass) errs()<<"\n finally got bitcase as:"<<*bitcast_arg<<"\n and stored arg::"<<*stored_arg;
            Type *ptr_i8 = PointerType::get(Type::getInt8Ty(thisMod->getContext()), 0);
            llvm::Type *ArgTypes[] = { ptr_i8,ptr_i8 }	;
            Function *vprintfFunction =dyn_cast<Function>( thisMod->getOrInsertFunction("vprintf",
                        FunctionType::get(IntegerType::getInt32Ty(thisMod->getContext()),
                            ArgTypes,false /*
                                              this is var arg func type*/) 
                        ) );
            if (vprintfFunction == nullptr ) {
                if (debug_stride_pass) errs()<<"\n func def not found::";
                return;
            }
            if (debug_stride_pass) errs()<<"\n vprintf::"<<*vprintfFunction;
            Value* callinstr = builder.CreateCall(vprintfFunction,ArgsV  );

        }
        void print_instr(Value *v_instr ){
            if (Instruction *instr = dyn_cast<Instruction>(v_instr) ){
                if (!(instr->getOpcode() == Instruction::ZExt|| instr->getOpcode() == Instruction::SExt))
                    errs()<<" ::"<<*v_instr;
                for (int i=0,n=instr->getNumOperands(); i< n ; i++ ){
                    Value *op = instr->getOperand(i);
                    print_instr(op);
                }
            }
        }
        bool check_if_index_const(Value *v_instr,std::set<Value*> &visited_set ){
            if (visited_set.find(v_instr) != visited_set.end() )    return true ;
            visited_set.insert(v_instr);
            if (Instruction *instr = dyn_cast<Instruction>(v_instr) ){

                if (dyn_cast<CallInst>(instr)) 
                    return  check_if_block_dim_call(instr);//const iff a block dim, else not const
                else if ( PHINode *index_phi = dyn_cast<PHINode>(instr)) {
                    Value *init_loop  = index_phi->getIncomingValue(0 ); //TODO verify if this is always 0, or 1, by checking the basicblock
                    return check_if_index_const(init_loop, visited_set);
                }else if (instr->mayReadOrWriteMemory()) return false;

                for (int i=0,n=instr->getNumOperands(); i< n ; i++ ){
                    Value *op = instr->getOperand(i);
                    if (!check_if_index_const(op, visited_set)) return false;
                }
            }
            return true ;
        }
        bool check_if_back_edge(Instruction *instr,std::set<Instruction*> &visited_set ){
            if (visited_set.find(instr) != visited_set.end() )    return false;
            visited_set.insert(instr);

            if (dyn_cast<CallInst>(instr)) 
                return  false;//No back edge 
            else if ( PHINode *index_phi = dyn_cast<PHINode>(instr) ) {
                return true;//Reached another phi node, cannot handle this 
            }

            for (int i=0,n=instr->getNumOperands(); i< n ; i++ ){
                Value *op = instr->getOperand(i);
                if (Instruction *op_instr = dyn_cast<Instruction>(op) ){
                    if (check_if_back_edge( op_instr , visited_set)) return true;
                }
            }
            return false;
        }

        bool check_if_block_dim_call (Instruction*instr ){
            if (instr == nullptr) return false;
            if (CallInst *callerI = dyn_cast<CallInst>(instr)) {//TODO add check here for  @llvm.nvvm.read.ptx.sreg.ctaid.x()
                Function * calledFunc = callerI->getCalledFunction();
                StringRef functionName = calledFunc->getName();
                //StringRef XblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.x" ) ;
                //StringRef YblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.y" ) ;
                //StringRef ZblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.z" ) ;
                StringRef xthreadim("llvm.nvvm.read.ptx.sreg.ntid.x");
                StringRef ythreadim("llvm.nvvm.read.ptx.sreg.ntid.y");
                StringRef zthreadim("llvm.nvvm.read.ptx.sreg.ntid.z");
                if (functionName.equals(xthreadim) ||functionName.equals(ythreadim)||functionName.equals(zthreadim)){
                    return true;
                }
            }
            return false;
        }
        void set_if_block_index_instr (Instruction*instr ){
            if (instr == nullptr) return;
            if (CallInst *callerI = dyn_cast<CallInst>(instr)) {//TODO add check here for  @llvm.nvvm.read.ptx.sreg.ctaid.x()
                if (callerI->isInlineAsm()) return;
                Function * calledFunc = callerI->getCalledFunction();
                if (calledFunc == nullptr ) return ;
                StringRef functionName = calledFunc->hasName() ? calledFunc->getName():"";
                //StringRef XblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.x" ) ;
                //StringRef YblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.y" ) ;
                //StringRef ZblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.z" ) ;
                //StringRef xthreadin("llvm.nvvm.read.ptx.sreg.tid.x");
                //StringRef ythreadin("llvm.nvvm.read.ptx.sreg.tid.y");
                //StringRef zthreadin("llvm.nvvm.read.ptx.sreg.tid.z");
                if (functionName.equals(XblockIdxString )  ||functionName.equals(YblockIdxString )||
                        functionName.equals(ZblockIdxString )||functionName.equals(xthreadin) ||functionName.equals(ythreadin)||functionName.equals(zthreadin)){
                    got_block_index_instr = true;
                    return ;
                }
            }
        }
        GlobalVariable *getStringRef(std::string print_msg ) {
            Module *M = thisMod;
            // Create a constant internal string reference...
            if (debug_stride_pass) errs()<<"\n get global for ::"<<print_msg;
            Constant *Init =ConstantDataArray::getString(M->getContext(),print_msg);
            // Create the global variable and record it in the module
            // The GV will be renamed to a unique name if needed.
            GlobalVariable *GV = new GlobalVariable(Init->getType(), true,
                    GlobalValue::InternalLinkage, Init,
                    "trstr");
            M->getGlobalList().push_back(GV);
            return GV;
        }
        int get_init_const_value() {return 0;}
        bool  get_block_stride_instr (Instruction *instr,IRBuilder<> &builder, Value *&return_val_stride ) {
            if (visit_done_set.find(instr )!= visit_done_set.end() ){
                return_val_stride = instr;
                return false;
            }
            if (cannot_compute) return false;
            visit_done_set.insert(instr);
            if (debug_stride_pass) errs()<<"\n Called with ::"<<*instr<<"\n-----\n";

            if (CallInst *callerI = dyn_cast<CallInst>(instr)) {//TODO add check here for  @llvm.nvvm.read.ptx.sreg.ctaid.x()
                Function * calledFunc = callerI->getCalledFunction();
                StringRef functionName = calledFunc->getName();
                if (functionName.equals(XblockIdxString )  && block_stride_X==1){
                    ConstantInt  *initializeIndex = llvm::ConstantInt::get(IntegerType::get (instr->getContext(), 32),1);// llvm::APInt(/*nbits*/32, value, /*bool*/is_signed));
                    return_val_stride = initializeIndex ;
                    //block_index_found=true;
                    //errs()<<"\n got a call with const::"<<*initializeIndex<<" \n Called functin with name::"<<calledFunc->getName();
                    if (debug_stride_pass) errs()<<"\n Returning true with ::"<<*return_val_stride;
                    return true;
                } else if (functionName.equals(YblockIdxString ) && block_stride_X==2 ) { //TODO  handle the case when block stride is along Y or Z
                    ConstantInt  *initializeIndex = llvm::ConstantInt::get(IntegerType::get (instr->getContext(), 32),1);// llvm::APInt(/*nbits*/32, value, /*bool*/is_signed));
                    //block_index_found=true;
                    return_val_stride = initializeIndex ;
                    //errs()<<"\n got a call with const::"<<*initializeIndex<<" \n Called functin with name::"<<calledFunc->getName();
                    if (debug_stride_pass) errs()<<"\n Returning true with ::"<<*return_val_stride;
                    return true;
                } 
                else    if (functionName.equals(xthreadDim) ) {
                    XblockDim = callerI;
                } else if( functionName.equals(ythreadDim) ){
                    YblockDim = callerI;
                }
                return_val_stride = instr ;
                //if (debug_stride_pass) errs()<<"\n got a call with const::"<<*initializeIndex<<" \n Called functin with name::"<<calledFunc->getName();
                if (debug_stride_pass) errs()<<"\n Returning false with ::"<<*return_val_stride;
                return false;
            }else if (instr->isBinaryOp() ) { // Which other binary ops to handle ?
                //if (debug_stride_pass) errs()<<"\n got instruction with bin op::"<<*instr;
                Value *op1 = instr->getOperand(0);
                Value *op2 = instr->getOperand(1);
                bool is_op2_index = false, is_op1_index = false;
                if (Instruction *parentInstr = dyn_cast<Instruction>(op1)) {
                    if (parentInstr != instr )
                        //if (debug_stride_pass) errs()<<"\n before::"<<*op1;
                        is_op1_index = get_block_stride_instr(parentInstr, builder, op1 );
                    if (is_op1_index) if (debug_stride_pass) errs()<<"\n After::"<<*op1;
                }
                if (Instruction *parentInstr = dyn_cast<Instruction>(op2)) {
                    if (parentInstr != instr )
                        //if (debug_stride_pass) errs()<<"\n Before:"<<*op2;
                        is_op2_index = get_block_stride_instr(parentInstr, builder, op2 );
                    if (is_op2_index) if (debug_stride_pass) errs()<<"\n After::"<<*op2;
                }
                //if (debug_stride_pass) errs()<<"\n new instruction created::"<<is_op1_index<<" "<<is_op2_index;
                //if (debug_stride_pass) errs()<<"\nop1::"<<*op1<<" op2::"<<*op2;
                if (op1->getType() != op2->getType())
                    op1 = builder.CreateSExt(op2, op1->getType());
                if ( (is_op2_index | is_op1_index ) && (instr->getOpcode() == Instruction::Add || instr->getOpcode()
                            == Instruction::FAdd || instr->getOpcode() == Instruction::Sub ||instr->getOpcode() ==
                            Instruction::FSub )
                        /*  !(instr->getOpcode() == Instruction::Mul || instr->getOpcode() == Instruction::Shl ||
                            instr->getOpcode() == Instruction::UDiv ||
                            instr->getOpcode() == Instruction::SDiv || 
                            instr->getOpcode() == Instruction::LShr) */
                   ) {//TODO handle when index op2
                    if  (is_op2_index & is_op1_index) return_val_stride = builder.CreateBinOp(Instruction::BinaryOps(instr->getOpcode()), op1, op2, "tmp_stride_compute");
                    else if (is_op1_index) return_val_stride = op1;
                    else if (is_op2_index) return_val_stride = op2;
                } else if ( (is_op2_index ^ is_op1_index) &&   ( (instr->getOpcode() == Instruction::Mul ) ||
                            (is_op1_index  && ( instr->getOpcode() == Instruction::Shl ||
                                                instr->getOpcode() == Instruction::UDiv ||
                                                instr->getOpcode() == Instruction::SDiv || 
                                                instr->getOpcode() == Instruction::LShr))) ){
                    unsigned instr_opcode= instr->getOpcode();
                    Value *operand_2_mod = op2;
                    if (instr->getOpcode() == Instruction::Shl ||instr->getOpcode() == Instruction::LShr) {
                        instr_opcode = (instr_opcode == Instruction::Shl )? (Instruction::Mul):(Instruction::UDiv);
                        Value *t= llvm::ConstantInt::get(IntegerType::get (instr->getContext(), 32),1);// llvm::APInt(/*nbits*/32, value, /*bool*/is_signed));
                        if (t->getType() != op2->getType()) t = builder.CreateSExt(t, op2->getType());

                        operand_2_mod=  builder.CreateBinOp(Instruction::Shl, t, op2, "tmp_stride_compute");
                        if (debug_stride_pass) errs()<<"\n shift::"<<*operand_2_mod;
                    }
                    return_val_stride = builder.CreateBinOp(Instruction::BinaryOps(instr_opcode ), op1, operand_2_mod, "tmp_stride_compute");
                    if (debug_stride_pass) errs()<<"\n Mul returning::"<<*return_val_stride;
                } else if ( is_op2_index || is_op1_index ) {
                    cannot_compute = true;
                    errs()<<"\n Cannot Compute::"<<*instr;
                    return false;
                }
                else {
                    return_val_stride = builder.CreateBinOp(Instruction::BinaryOps(instr->getOpcode()), op1, op2, "tmp_stride_compute");
                    //if ( (instr->getOpcode() == Instruction::Mul || instr->getOpcode() == Instruction::Shl) &&
                    //    is_op2_index && is_op2_index ){//Non Affine
                    //    cannot_compute = true;
                    //    return false;}
                }
                if (debug_stride_pass) errs()<<"\n Returning "<<(is_op2_index || is_op1_index) <<" with ::"<<*return_val_stride;
                return is_op2_index || is_op1_index;
            }else if ( PHINode *index_phi = dyn_cast<PHINode>(instr)) {
                return_val_stride = index_phi->getIncomingValue(0 ); //TODO verify if this is always 0, or 1, by checking the basicblock
                if (got_a_phi_node) {//Cannot handle mutiple loops/if else blocks for index
                    cannot_compute=true;
                    return false;
                }
                /*We can handle both the incmoing values, if the second is only an addition then specialy, but the added
                 * value must not depend on block index, if it depends then block stride will vary on each loop
                 * iteration*/
                got_a_phi_node=true;

                std::set<Instruction*> visited_set;
                if (Instruction *index_instr = dyn_cast<Instruction>(return_val_stride)) {
                    if (check_if_back_edge(index_instr,visited_set )) {
                        if (debug_stride_pass)  errs()<<"\n Oops got a back edge, trying other edge"<<*return_val_stride;
                        if (index_phi->getNumIncomingValues() ==1) {
                            cannot_compute= true;
                            return false;

                        }
                        return_val_stride = index_phi->getIncomingValue(1 ); //TODO verify if this is always 0, or 1, by checking the basicblock                    
                        if (check_if_back_edge(index_instr,visited_set )) {
                            if (debug_stride_pass)    errs()<<"\n still a back edge::"<<*return_val_stride;
                            cannot_compute= true;
                            return false;
                        }
                    }
                }
                if (Instruction *index_instr = dyn_cast<Instruction>(return_val_stride)) {
                    bool is_index =get_block_stride_instr(index_instr, builder, return_val_stride);
                    if (debug_stride_pass) errs()<<"\n Phi Node Returning with ::"<<*return_val_stride;
                    return is_index;
                }
                if (debug_stride_pass) errs()<<"\n Returning with ::"<<*return_val_stride;
                return false;
            } else if (  LoadInst *ld = dyn_cast<LoadInst>(instr )) {
                Value* addr = ld->getPointerOperand();
                std::set<Value*> visited_set;
                bool is_index_const = check_if_index_const(addr, visited_set);
                if (is_index_const) 
                    return_val_stride = ld;
                cannot_compute = !is_index_const;
                return is_index_const;
                //get_block_stride_instr(addr,builder,return_val_stride );
                //instr->mayReadOrWriteMemory() ) 
                //cannot_compute = true ;
            } else if (  SelectInst *SI = dyn_cast<SelectInst>(instr )) {

                //CmpInst *CmpI = dyn_cast<CmpInst>(SI->getCondition());TODO  Need to handle if else instructions
                Value *TrueVal = SI->getTrueValue();
                if (Instruction *i = dyn_cast<Instruction>(TrueVal) ) {
                    bool is_index =get_block_stride_instr(i, builder, return_val_stride);
                    if (is_index) return true;
                }
                Value *FalseVal = SI->getFalseValue();
                if (Instruction *i = dyn_cast<Instruction>(FalseVal) ) {
                    bool is_index =get_block_stride_instr(i, builder, return_val_stride);
                    if (is_index) return true;
                }
                return false;
            } else  { 
                if (instr->getNumOperands()==1 ) {
                    Instruction *cloned_copy = instr->clone();
                    Value *dupVal = instr->getOperand(0);
                    if (Instruction *i = dyn_cast<Instruction>(dupVal ) ) {
                        bool is_index = get_block_stride_instr(i, builder, dupVal );
                        cloned_copy->setOperand(0,dupVal );
                        return_val_stride =  builder.Insert(cloned_copy );
                        if (debug_stride_pass) errs()<<"\n Returning "<<is_index<<"with ::"<<*return_val_stride;
                        return is_index;
                    }
                }
            }
            return_val_stride =  instr;
            if (debug_stride_pass) errs()<<"\n Returning false with ::"<<*return_val_stride;
            return false;
        }

        // We don't modify the program, so we preserve all analyses.
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            //AU.setPreservesCFG();
            ////    AU.setPreservesAll();
            //AU.addRequired<TargetLibraryInfoWrapperPass>();
            //AU.addRequired<DominatorTreeWrapperPass>();
            //AU.addRequired<CallGraphWrapperPass>();
            //AU.addRequired<LoopInfoWrapperPass>();
            //getLoopAnalysisUsage(AU);
        }
    };
}

char ComputeBlockStride::ID=0;
static RegisterPass<ComputeBlockStride>
MY("compute_block_stride", "Compute Block Stride CUDA");

static void registerComputeStridePass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
/*PassRegistry &Registry = *PassRegistry::getPassRegistry();
   initializeAnalysis(Registry);
initializeCore(Registry);
                initializeScalarOpts(Registry);
                initializeIPO(Registry);
                initializeAnalysis(Registry);
                initializeIPA(Registry);
                initializeTransformUtils(Registry);
                initializeInstCombine(Registry);
                initializeInstrumentation(Registry);
                initializeTarget(Registry);*/
  PM.add(new ComputeBlockStride());
}
//static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible, registerComputeStridePass);
//static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,registerComputeStridePass);
//static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_LoopOptimizerEnd,registerComputeStridePass);
static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_ScalarOptimizerLate,registerComputeStridePass);
//static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_OptimizerLast,registerComputeStridePass);
//namespace {
//  // Hello - The first implementation, without getAnalysisUsage.
//  struct Hello : public FunctionPass {
//    static char ID; // Pass identification, replacement for typeid
//    Hello() : FunctionPass(ID) {}
//
//    bool runOnFunction(Function &F) override {
//      ++HelloCounter;
//      if (debug_stride_pass) errs() << "Hello: func1 ";
//      errs().write_escaped(F.getName()) << '\n';
//      return false;
//    }
//  };
//}
//
//char Hello::ID = 0;
//static RegisterPass<Hello> X("hello", "Hello World Pass");
//
//namespace {
//  // Hello2 - The second implementation with getAnalysisUsage implemented.
//  struct Hello2 : public FunctionPass {
//    static char ID; // Pass identification, replacement for typeid
//    Hello2() : FunctionPass(ID) {}
//
//    bool runOnFunction(Function &F) override {
//      ++HelloCounter;
//      errs() << "Hello function2 by prithayan: ";
//      errs().write_escaped(F.getName()) << '\n';
//      return false;
//    }
//
//    // We don't modify the program, so we preserve all analyses.
//    void getAnalysisUsage(AnalysisUsage &AU) const override {
//      AU.setPreservesAll();
//    }
//  };
//}
//
//char Hello2::ID = 0;
//static RegisterPass<Hello2>
//Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");
//
//
//
//
//namespace {
//  // Loop_info : this pass will analyze the loop index and print instructions that use the loop index
//
//  struct mem_stride_info{
//      //memory and the UB and the index stride
//      std::set<unsigned int> mem_argNums;
//      const SCEV *upperBound;
//      const SCEV *stepRecr;
//  };
//  std::map<Function*, mem_stride_info*> functionStrideMap;
//  struct MyLoopInfo : public LoopPass {
//  static char ID; // Pass identification, replacement for typeid
//  Module *thisModule;
//  MyLoopInfo () : LoopPass(ID) {
//      thisModule = nullptr;
//
//  }
//
//  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
//      //const Function *   getParent () const
//      auto *SE = getAnalysisIfAvailable<ScalarEvolutionWrapperPass>();
//      AnalyzeThisLoop(L,
//              &getAnalysis<AAResultsWrapperPass>().getAAResults(),
//              &getAnalysis<LoopInfoWrapperPass>().getLoopInfo(),
//              &getAnalysis<DominatorTreeWrapperPass>().getDomTree(),
//              &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(),
//              SE ? &SE->getSE() : nullptr, false);
//      std::map< Function*, mem_stride_info*>::iterator it;
//      for (it = functionStrideMap.begin() ; it!= functionStrideMap.end(); it++ ){
//          errs()<<"\n Function ::"<<(it->first)->getName();
//          errs()<<"\n upper bound:"<<*(it->second->upperBound);
//      }
//      //  Function *F = it->first;
//      //  if (F == nullptr) continue;
//      //  if (!( F->begin())) continue;
//      //  inst_iterator I    = inst_begin(F);
//      //  Instruction *instr = &*I; 
//      //  Module *M = instr->getModule();
//      //Module *M = functionStrideMap.begin()->first->getParent();
//      //insertStride_atMalloc(thisModule );
//      return true ;
//  }
//  static std::string getPrintfCodeFor(const Value *V) {
//      if (V == 0) return "";
//      if (V->getType()->isFloatTy())
//          return "%g";
//      else if (V->getType()->isIntegerTy())
//          return "%d";
//      assert(0 && "Illegal value to print out...");
//      return "";
//  }
//  static inline GlobalVariable *getStringRef(Module *M, const std::string &str) {
//      // Create a constant internal string reference...
//      Constant *Init =ConstantDataArray::getString(M->getContext(),str);
//      // Create the global variable and record it in the module
//      // The GV will be renamed to a unique name if needed.
//      GlobalVariable *GV = new GlobalVariable(Init->getType(), true,
//              GlobalValue::InternalLinkage, Init,
//              "trstr");
//      M->getGlobalList().push_back(GV);
//      return GV;
//  }
//
////  static void InsertPrintInst(Value *V,  Instruction *InsertBefore,
////                              std::string Message,
////                              Function *Printf) {
////      // Escape Message by replacing all % characters with %% chars.
////      BasicBlock *BB = InsertBefore->getParent();
////      std::string Tmp;
////      std::swap(Tmp, Message);
////      std::string::iterator I = std::find(Tmp.begin(), Tmp.end(), '%');
////      while (I != Tmp.end()) {
////          Message.append(Tmp.begin(), I);
////          Message += "%%";
////          ++I; // Make sure to erase the % as well...
////          Tmp.erase(Tmp.begin(), I);
////          I = std::find(Tmp.begin(), Tmp.end(), '%');
////      }
////      Message += Tmp;
////      Module *Mod = BB->getParent()->getParent();
////      // Turn the marker string into a global variable...
////      GlobalVariable *fmtVal = getStringRef(Mod,
////              Message+getPrintfCodeFor(V)+"\n");
////      // Turn the format string into an sbyte *
////      Constant *GEP=ConstantExpr::getGetElementPtr(fmtVal,
////              std::vector<Constant*>(2,Constant::getNullValue(Type::getInt64Ty(BB->getContext()))));
////      // // Insert a call to the hash function if this is a pointer value
////      // if (V && isa<PointerType>(V->getType()) && !DisablePtrHashing)
////      // {
////      //     const Type *SBP = PointerType::get(Type::SByteTy);
////      //     if (V->getType() != SBP)     // Cast pointer
////      //         to be sbyte*
////      //             V = new CastInst(V, SBP,
////      //                     "Hash_cast", InsertBefore);
////      //     std::vector<Value*> HashArgs(1,
////      //             V);
////      //     V = new
////      //         CallInst(HashPtrToSeqNum,
////      //                 HashArgs, "ptrSeqNum",
////      //                 InsertBefore);
////      // }
////      // Insert the first       print instruction to           print the string flag:
////      std::vector<Value*>           PrintArgs;
////      PrintArgs.push_back(GEP);
////      if (V)
////          PrintArgs.push_back(V);
////          CallInst *call_print = CallInst::Create(Printf, PrintArgs, "trace", InsertBefore);
////  }
////
////    Function *  getPrintfFunc(Module *M ) {
////      const Type *SBP = PointerType::get(Type::SByteTy);
////      const FunctionType *MTy = FunctionType::get(Type::IntTy, std::vector<const Type*>(1,SBP), true);
////      Function* printfFunc =M->getOrInsertFunction("printf", MTy);
////      return printfFunc;
////  }
//
//  void insertStride_atMalloc( Module *M){
//      Module::iterator it;
//      Module::iterator end = M->end();                                                                                                                                     
//	//Function* printfFunc =cast<Function>( M->getOrInsertFunction("printf"));
//	//Function* printfFunc =cast<Function>( M->getFunction("printf"));
//   // Function *printfFunc = getPrintfFunc(M );
//   // if (printfFunc!= nullptr)
//   // errs()<<"\n printf functin is :: "<<*printfFunc;
//
//      for (it = M->begin(); it != end; ++it) {
//          Function *F = &*it;
//          errs()<<"\n function::"<<*F;
//          errs()<<"=====================================";
//          for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
//              Instruction *instr = &*I;
//              errs() << *instr << "\n";
//              if (isa<CallInst>(instr)) {
//                  CallInst *calledI = dyn_cast<CallInst>(instr);
//                  IRBuilder<> builder(instr);
//                  if ( Function *F = calledI->getCalledFunction()) {
//                      std::map< Function*, mem_stride_info*>::iterator it = functionStrideMap.find(F) ;
//                      if (it != functionStrideMap.end() ) {
//                          errs()<<"\n got called func is ::"<<F->getName();
//                          const SCEV *UB = it->second->upperBound;
//                          Value *insertedinstr = createInstr_SCEV (UB, calledI, builder ) ;
//                          //InsertPrintInst(insertedinstr , instr, "upper bound is", printfFunc   );
//
//                         // if (printfFunc != nullptr)
//                         //     builder.CreateCall(printfFunc,  printf_arg_values );
//                          errs()<<"\n inserted the Instr::"<<*insertedinstr;
//                      }
//                  }
//              }
//          }
//      }
//      return ;
//  }
//
//              //  for (auto      &bb : iter->getBasicBlockList() ) {
//              //      //const BasicBlock *basicb = dyn_cast<BasicBlock>(bb);
//              //      for (auto i=bb.begin(); i!=bb.end();i++) {
//              //          Instruction *instr = dyn_cast<Instruction>(&i);
//              //          errs() <<"\n instruction is ::"<<*i;
//              //          //if (Instruction *instr = dyn_cast<Instruction*>( i)){
//              //          //errs() <<" \n instr::"<<instr;
//              //          //}
//
//              //      }
//              //  }
//
//  /// This transformation requires natural loop information & requires that
//  /// loop preheaders be inserted into the CFG...
//  ///
//  void getAnalysisUsage(AnalysisUsage &AU) const override {
//      AU.setPreservesCFG();
////    AU.setPreservesAll();
//    AU.addRequired<TargetLibraryInfoWrapperPass>();
//    getLoopAnalysisUsage(AU);
//  }
//
//
//private:
//
//
//
//// //define a extern function "printf"
//// static llvm::Function*	
//// printf_prototype(llvm::LLVMContext& ctx, llvm::Module *mod)
//// {
//// 		std::vector<llvm::Type*> printf_arg_types;
//// 		printf_arg_types.push_back(llvm::Type::getInt32Ty(ctx));
//// 
//// 		llvm::FunctionType* printf_type =
//// 			llvm::FunctionType::get(llvm::Type::getInt32Ty(ctx), printf_arg_types, true);
//// 
//// 		llvm::Function *func = llvm::Function::Create(printf_type, llvm::Function::ExternalLinkage,
////         llvm::Twine("printf"),mod);
//// 		func->setCallingConv(llvm::CallingConv::C);
//// 	return func;
//// }
////
//////get a printf function
////Function* Get_print()
////{
////	LLVMContext& ctx = llvm::getGlobalContext();
////	Module* mod = new Module("test",ctx);
//////	constant* c = mod->getorinsertfunction("printf");
////	Function *printf_func = printf_prototype(ctx, mod);	
////	printf_func->setCallingConv(CallingConv::C);
////	return printf_func;
////}
//
//  Value*createInstr_SCEV (const SCEV *V, CallInst *calledInstr, IRBuilder<> &builder ) {
//      /*find the kind of scev, 
//        then based on the values used, try to map it to function argument, then find the value of the arguemnt from
//        calling function and use that.  Number to value mapping*/
//
//      unsigned scevT =   (V->getSCEVType());
//      Instruction::BinaryOps optype=Instruction::Add;
//
//      switch (static_cast<SCEVTypes>(scevT) ) {
//          case scUnknown: {
//                              const SCEVUnknown *LU = cast<SCEVUnknown>(V);
//                              const Value *LV = LU->getValue();
//                              errs()<<"\n Unknown Value::"<<*LV;
//                              if (const Argument *LA = dyn_cast<Argument>(LV)) {
//                                  errs() <<"\n argument::"<<*LA<<"\t argument number is ::"<<LA->getArgNo();
//                                  //getCalledFunction getFunction
//
//                                  int n=  LA->getArgNo();
//                                  Value *sentArg = calledInstr->getArgOperand (n ) ;
//                                  errs()<<"\n Value of arg from calling func ::"<< *sentArg;
//                                  return sentArg;
//                              }
//                              break;//TODO handle below cases
//                              if (const Instruction *LInst = dyn_cast<Instruction>(LV)) {
//                                  errs() <<"\n Error is instruction Not suppoerted::"<<*LInst;
//                                  unsigned LNumOps = LInst->getNumOperands();
//                                  errs() <<"\n num ops::"<<LNumOps;
//                                  return  nullptr;
//                              }
//                              if (bool LIsPointer = LV->getType()->isPointerTy()){
//                                  errs() <<"\n Error Pointer type bound not handled::"<<LIsPointer;
//                                  return nullptr;
//                              }
//                          }
//                          break   ;
//          case scConstant: {
//                               const SCEVConstant *LC = cast<SCEVConstant>(V);
//                               ConstantInt *constVal = LC->getValue();
//                               errs()<<"\n const val::"<<*constVal;
//                               return constVal;
//                           }
//                           break;
//                           break;
//          case scAddExpr:  optype = Instruction::Add;
//          case scMulExpr:  if (optype !=Instruction::Add) optype = Instruction::Mul;
//                           {
//                               const SCEVNAryExpr *NAry = cast<SCEVNAryExpr>(V);
//                               const char *OpStr = nullptr;
//                               /*switch (NAry->getSCEVType()) {
//                                 case scAddExpr: OpStr = " + "; break;
//                                 case scMulExpr: OpStr = " * "; break;
//                                 case scUMaxExpr: OpStr = " umax "; break;
//                                 case scSMaxExpr: OpStr = " smax "; break;
//                                 }*/
//                               const SCEVNAryExpr *LC = cast<SCEVNAryExpr>(V);
//                               errs() <<"\n scev nary::"<<*LC;
//
//                               // Lexicographically compare n-ary expressions.
//                               unsigned LNumOps = LC->getNumOperands();
//                               if (LNumOps == 2) {
//                                   const SCEV *scevA = LC->getOperand(0);
//                                   const SCEV *scevB = LC->getOperand(1);
//                                   Value *x = createInstr_SCEV(scevA, calledInstr, builder);
//                                   Value *y =createInstr_SCEV(scevB, calledInstr, builder) ;
//                                   if (x!= nullptr && y!= nullptr ) {
//                                       errs()<<"\n got operand instructions as ::"<<*x<<"\n and::"<<*y;
//                                       if (x->getType() != y->getType())
//                                           y = builder.CreateSExt(y, x->getType());
//                                       Value* tmp = builder.CreateBinOp(optype, x, y, "tmp");
//                                       errs()<<"\n got final instr::"<<*tmp;
//                                       return tmp;
//                                   }
//                               }
//
//                               // for (unsigned i = 0; i != LNumOps; ++i) {
//                               //     const SCEV *recV = LC->getOperand(i);
//                               //     errs()<<"\n op::"<<*(recV);
//                               //     printSCEVInfo(recV);
//                               // }
//                           }
//                           break;
//
//          case scUDivExpr: {
//                               const SCEVUDivExpr *LC = cast<SCEVUDivExpr>(V);
//
//                               errs()<<"\n udiv expr::"<<*LC<<"\n lhs as::"<<*(LC->getLHS());
//                           }
//                           break;
//
//          case scTruncate:{
//                              const SCEVCastExpr *LC = cast<SCEVCastExpr>(V);
//                              const SCEV *recV = LC->getOperand();
//                              errs()<<"\n sign truncate"<<*(recV);
//                              Value *v =  createInstr_SCEV(recV, calledInstr, builder );
//                              Value *truncV = builder.CreateTrunc(v, v->getType() );
//                                errs()<<"and the instruction is ::"<<*truncV;
//                              return truncV;
//                          }
//          case scZeroExtend:{
//                                const SCEVCastExpr *LC = cast<SCEVCastExpr>(V);
//                                const SCEV *recV = LC->getOperand();
//                                errs()<<"\n sign zero extend::"<<*(recV);
//                                Value *v =  createInstr_SCEV(recV, calledInstr, builder );
//                                Value *signZV = builder.CreateZExt(v, v->getType() );
//                                errs()<<"and the instruction is ::"<<*signZV;
//                                return signZV;
//                            }
//          case scSignExtend: {
//                                 const SCEVCastExpr *LC = cast<SCEVCastExpr>(V);
//
//                                 // Compare cast expressions by operand.
//                                 const SCEV *recV = LC->getOperand();
//                                 errs()<<"\n sign extend::"<<*(recV);
//                                 Value *v =  createInstr_SCEV(recV, calledInstr, builder );
//                                 Value *signV = builder.CreateSExt(v, v->getType() );
//                                errs()<<"and the instruction is ::"<<*signV;
//                                 return signV;
//                             }
//                             break;
//          case scAddRecExpr: errs()<<"\n recr expr"; break;
//                             //{                       const SCEVAddRecExpr *LA = cast<SCEVAddRecExpr>(V);
//                             //
//
//                             //                       // Compare addrec loop depths.
//                             //                       const Loop *LLoop = LA->getLoop();
//                             //                       unsigned LDepth = LLoop->getLoopDepth();
//
//                             //                       // Addrec complexity grows with operand count.
//                             //                       unsigned LNumOps = LA->getNumOperands();
//                             //                       errs()<<"\n addrecexpr::"<<*LA<<"\n lloop::"<< *LLoop<<"\n LDepth::"<<LDepth;
//
//                             //                       // Lexicographically compare.
//                             //                       for (unsigned i = 0; i != LNumOps; ++i) {
//                             //                           const SCEV *recV = LA->getOperand(i);
//                             //                           errs()<<"\n op::"<<*(recV);
//                             //                           printSCEVInfo(recV);
//                             //                       }
//
//                             //                   }
//          case scCouldNotCompute:
//                             errs()<<"\n Could not compute";
//      }
//
//      return nullptr;
//  }
///*
//  void construct_bound_expr (const SCEV *V, expression_tree &expression, bool is_left) {
//
//      unsigned scevT =   (V->getSCEVType());
//      switch (static_cast<SCEVTypes>(scevT) ) {
//          case scUnknown: {
//                              const SCEVUnknown *LU = cast<SCEVUnknown>(V);
//
//                              // Sort SCEVUnknown values with some loose heuristics. TODO: This is
//                              // not as complete as it could be.
//                              const Value *LV = LU->getValue();
//                              errs()<<"\n Unknown Value::"<<*LV;
//
//                              // Order pointer values after integer values. This helps SCEVExpander
//                              // form GEPs.
//                              if (bool LIsPointer = LV->getType()->isPointerTy()){
//                                  errs() <<"\n Error Pointer type bound not handled::"<<LIsPointer;
//                                  return ;
//                              }
//
//                              // Compare getValueID values.
//                              if (  LV->getValueID()) {
//                                  errs() << "\n value id not handled ::"<<LV->getValueID();
//                                  return;
//                                  }
//
//                              // Sort arguments by their position.
//                              if (const Argument *LA = dyn_cast<Argument>(LV)) {
//                                  errs() <<"\n argument::"<<*LA<<"\t argument number is ::"<<LA->getArgNo();
//                                  //getCalledFunction getFunction
//
//                                  int n=  LA->getArgNo();
//                                  expression.add_new_node(node_kind_type::ARGUMENT,&n , is_left);
//                                  return;
//                              }
//
//                              // For instructions, compare their loop depth, and their operand
//                              // count.  This is pretty loose.
//                              if (const Instruction *LInst = dyn_cast<Instruction>(LV)) {
//                                  errs() <<"\n Error is instruction Not suppoerted::"<<*LInst;
//                                  unsigned LNumOps = LInst->getNumOperands();
//                                  errs() <<"\n num ops::"<<LNumOps;
//                                  return;
//                              }
////dyn_cast<GlobalValue>(V)
//                              // Compare the number of operands.
//                          }
//                          break   ;
//          case scConstant: {
//                               const SCEVConstant *LC = cast<SCEVConstant>(V);
//
//                               // Compare constant values.
//                               const APInt &LA = LC->getAPInt();
//                                  expression.add_new_node(node_kind_type::CONST   ,LC , is_left);
//                               errs()<<"\n const val::"<<*LC<<"\t apiint::"<<LA;
//                           }
//                           break;
//          case scAddRecExpr: {
//                                 const SCEVAddRecExpr *LA = cast<SCEVAddRecExpr>(V);
//
//                                 // Compare addrec loop depths.
//                                 const Loop *LLoop = LA->getLoop();
//                                 unsigned LDepth = LLoop->getLoopDepth();
//
//                                 // Addrec complexity grows with operand count.
//                                 unsigned LNumOps = LA->getNumOperands();
//                                 errs()<<"\n addrecexpr::"<<*LA<<"\n lloop::"<< *LLoop<<"\n LDepth::"<<LDepth;
//
//                                 // Lexicographically compare.
//                                 for (unsigned i = 0; i != LNumOps; ++i) {
//                                     const SCEV *recV = LA->getOperand(i);
//                                     errs()<<"\n op::"<<*(recV);
//                                     printSCEVInfo(recV);
//                                 }
//
//                             }
//                             break;
//          case scAddExpr:
//          case scMulExpr:
//          case scSMaxExpr:
//          case scUMaxExpr: {
//                               const SCEVNAryExpr *LC = cast<SCEVNAryExpr>(V);
//                               errs() <<"\n scev nary::"<<*LC;
//
//                               // Lexicographically compare n-ary expressions.
//                               unsigned LNumOps = LC->getNumOperands();
//
//                               for (unsigned i = 0; i != LNumOps; ++i) {
//                                     const SCEV *recV = LC->getOperand(i);
//                                     errs()<<"\n op::"<<*(recV);
//                                     printSCEVInfo(recV);
//                               }
//                           }
//                           break;
//
//          case scUDivExpr: {
//                               const SCEVUDivExpr *LC = cast<SCEVUDivExpr>(V);
//
//                               errs()<<"\n udiv expr::"<<*LC<<"\n lhs as::"<<*(LC->getLHS());
//                           }
//                           break;
//
//          case scTruncate:
//          case scZeroExtend:
//          case scSignExtend: {
//                                 const SCEVCastExpr *LC = cast<SCEVCastExpr>(V);
//
//                                 // Compare cast expressions by operand.
//                                     const SCEV *recV = LC->getOperand();
//                                     errs()<<"\n sign extend::"<<*(recV);
//                                     printSCEVInfo(recV);
//                             }
//                             break;
//
//          case scCouldNotCompute:
//                             errs()<<"\n Could not compute";
//      }
//
//  }
//  */
////void LoopAccessInfo::collectStridedAccess(Value *MemAccess) 
////getStrideFromPointer
//  void printSCEVInfo (const SCEV *V) {
//
//      unsigned scevT =   (V->getSCEVType());
//      switch (static_cast<SCEVTypes>(scevT) ) {
//          case scUnknown: {
//                              const SCEVUnknown *LU = cast<SCEVUnknown>(V);
//
//                              // Sort SCEVUnknown values with some loose heuristics. TODO: This is
//                              // not as complete as it could be.
//                              const Value *LV = LU->getValue();
//                              errs()<<"\n Unknown Value::"<<*LV;
//
//                              // Order pointer values after integer values. This helps SCEVExpander
//                              // form GEPs.
//                              if (bool LIsPointer = LV->getType()->isPointerTy())
//                                  errs() <<"\n is pointer type ::"<<LIsPointer;
//
//                              // Compare getValueID values.
//                              if (  LV->getValueID())
//                                  errs() << "\n L value id ::"<<LV->getValueID();
//
//                              // Sort arguments by their position.
//                              if (const Argument *LA = dyn_cast<Argument>(LV)) {
//                                  errs() <<"\n argument::"<<*LA<<"\t argument number is ::"<<LA->getArgNo();
//                                  //getCalledFunction getFunction
//                              }
//
//                              // For instructions, compare their loop depth, and their operand
//                              // count.  This is pretty loose.
//                              if (const Instruction *LInst = dyn_cast<Instruction>(LV)) {
//                                  errs() <<"\n is instruction ::"<<*LInst;
//                                  unsigned LNumOps = LInst->getNumOperands();
//                                  errs() <<"\n num ops::"<<LNumOps;
//                              }
////dyn_cast<GlobalValue>(V)
//                              // Compare the number of operands.
//                          }
//                          break   ;
//          case scConstant: {
//                               const SCEVConstant *LC = cast<SCEVConstant>(V);
//
//                               // Compare constant values.
//                               const APInt &LA = LC->getAPInt();
//                               errs()<<"\n const val::"<<*LC<<"\t apiint::"<<LA;
//                           }
//                           break;
//          case scAddRecExpr: {
//                                 const SCEVAddRecExpr *LA = cast<SCEVAddRecExpr>(V);
//
//                                 // Compare addrec loop depths.
//                                 const Loop *LLoop = LA->getLoop();
//                                 unsigned LDepth = LLoop->getLoopDepth();
//
//                                 // Addrec complexity grows with operand count.
//                                 unsigned LNumOps = LA->getNumOperands();
//                                 errs()<<"\n addrecexpr::"<<*LA<<"\n lloop::"<< *LLoop<<"\n LDepth::"<<LDepth;
//
//                                 // Lexicographically compare.
//                                 for (unsigned i = 0; i != LNumOps; ++i) {
//                                     const SCEV *recV = LA->getOperand(i);
//                                     errs()<<"\n op::"<<*(recV);
//                                     printSCEVInfo(recV);
//                                 }
//
//                             }
//                             break;
//          case scAddExpr:
//          case scMulExpr:
//          case scSMaxExpr:
//          case scUMaxExpr: {
//                               const SCEVNAryExpr *LC = cast<SCEVNAryExpr>(V);
//                               errs() <<"\n scev nary::"<<*LC;
//
//                               // Lexicographically compare n-ary expressions.
//                               unsigned LNumOps = LC->getNumOperands();
//
//                               for (unsigned i = 0; i != LNumOps; ++i) {
//                                     const SCEV *recV = LC->getOperand(i);
//                                     errs()<<"\n op::"<<*(recV);
//                                     printSCEVInfo(recV);
//                               }
//                           }
//                           break;
//
//          case scUDivExpr: {
//                               const SCEVUDivExpr *LC = cast<SCEVUDivExpr>(V);
//
//                               errs()<<"\n udiv expr::"<<*LC<<"\n lhs as::"<<*(LC->getLHS());
//                           }
//                           break;
//
//          case scTruncate:
//          case scZeroExtend:
//          case scSignExtend: {
//                                 const SCEVCastExpr *LC = cast<SCEVCastExpr>(V);
//
//                                 // Compare cast expressions by operand.
//                                     const SCEV *recV = LC->getOperand();
//                                     errs()<<"\n sign extend::"<<*(recV);
//                                     printSCEVInfo(recV);
//                             }
//                             break;
//
//          case scCouldNotCompute:
//                             errs()<<"\n Could not compute";
//      }
//
//  }
//  const SCEV *letsComputeStride(Value *Ptr, ScalarEvolution *SE, Loop *Lp) {
//      errs() << "\n Computing Strid";
//      auto PtrTy = dyn_cast<PointerType>(Ptr->getType());
//      if (!PtrTy || PtrTy->isAggregateType()) {
//          errs() <<"\n not of poitner type::";
//          return nullptr;
//      }
//      Value *OrigPtr = Ptr;
//      int64_t PtrAccessSize = 1;
//      Ptr = stripGetElementPtr(Ptr, SE, Lp);
//      const SCEV *V =  SE->getSCEV(Ptr);
//      errs()   <<"\n ptr::"<<*Ptr<<" \n OrigPtr::"<<*OrigPtr;
//      errs() << "\n SCEV ::"<< *V;
//      if (Ptr != OrigPtr) //Strip off casts
//          while (const SCEVCastExpr *C = dyn_cast<SCEVCastExpr>(V))
//              V = C->getOperand();
//      //printSCEVInfo(V);
//
//      const SCEVAddRecExpr *S = dyn_cast<SCEVAddRecExpr>(V); 
//      if (!S) {
//          errs() << "\n oops not scevaddrecexpr typ";
//          return nullptr;
//      }
//      errs() <<"\n got SCEV add rec expr as ::"<< *S;
//      V = S->getStepRecurrence(*SE);
//      if (!V) {
//          errs()<< "\n OOps No step recurrence value";
//          return nullptr;
//      }
//      //class SCEVAddRecExpr : public SCEVNAryExpr :: has all important info
//      errs() <<"\n got step recurence as ::"<<*V;
//      return V;
//  }
//void runStrideComputation(Loop *L, AliasAnalysis *AA,
//                                        LoopInfo *LI, DominatorTree *DT,
//                                        TargetLibraryInfo *TLI,
//                                        ScalarEvolution *SE) {
//
//
//std::set<unsigned int> setOf_memory_arguments;
//    for (BasicBlock *BB : L->blocks()) 
//        for (Instruction &I : *BB)  {
//            if (thisModule == nullptr)
//            thisModule = I.getModule();
//                errs() << "\n "<< I;
//        }
//    errs()<<"\n=========================================";
//    for (BasicBlock *BB : L->blocks()) {
//        for (Instruction &I : *BB) {
//            GetElementPtrInst *gep;
//            if (gep = dyn_cast<GetElementPtrInst>(&I)) {
//                errs() <<"\n found gep::"<<*gep;
//                for (int i=0; i< gep->getNumOperands();i++) {
//                    Value *mem = gep->getOperand(i);
//                    errs() << "\n secondop is ::"<<*mem ;
//                    if  (const Argument *arg = dyn_cast<Argument>(mem)){
//                        unsigned int argn = arg->getArgNo();
//                        errs() <<"\n arguemtn numne ois ::"<<argn;
//                        setOf_memory_arguments.insert(argn);
//                    }
//                }
//            }
//            if (I.mayReadFromMemory() ) {
//                auto *Ld = dyn_cast<LoadInst>(&I);
//                if (!Ld || (!Ld->isSimple() ))
//                    continue;
//                LoadInst *Li = dyn_cast<LoadInst> (Ld);
//                Value *Ptr  = Li->getPointerOperand();
//                errs() << "\n Load ptr is ::"<<*Ptr;
//                errs() << "\n first op is ::"<<(I.getNumOperands());
//                for (int i=0; i< I.getNumOperands();i++) {
//                errs() << "\n secondop is ::"<<*Li->getOperand(i);
//                }
//                //errs() << "\n secondop is ::"<<*Li->getOperand(1);
//                //:getPtrStride
//                const SCEV  *stride = letsComputeStride(Ptr, SE, L);
//                if (!stride) continue;
//                errs() << "\n Stride is :"<< *stride;
//            }
//        }
//    }
//
//  errs() <<"\n is loop invariant back edge count?::"<<(SE->hasLoopInvariantBackedgeTakenCount(L));
////  errs() <<"\n backedgetakeninfo::"<<*(SE->getBackedgeTakenInfo());
//  if (SE->hasLoopInvariantBackedgeTakenCount(L)) {
//      const SCEV *UB = SE->getBackedgeTakenCount(L);
//      errs() << "\n bound::"<< *UB << "\n and type is ::"<<*(UB->getType())<<"\n and scevtype is :"<<UB->getSCEVType();
//      mem_stride_info *stride = new mem_stride_info; 
//      stride->mem_argNums = setOf_memory_arguments;
//      stride->upperBound = UB;
//      stride->stepRecr = NULL;
////      BlockT * bb = L->getBlocks()[0]->getParent();
//      Function *f = L->getBlocks()[0]->getParent();//bb->getParent();
//      functionStrideMap.insert(std::pair< Function*, mem_stride_info* > (f,stride ) );
//
//
//      printSCEVInfo(UB);
//      //construct_bound_expr(UB);
//  }
//
//  /*if (const SCEVAddExpr *Sum = dyn_cast<SCEVAddExpr>(UB)) {
//    // If Delta is a sum of products, we may be able to make further progress.
//    for (unsigned Op = 0, Ops = Sum->getNumOperands(); Op < Ops; Op++) {
//      const SCEV *Operand = Sum->getOperand(Op);
//      errs() <<"\n op of scev is ::"<<*Operand;
//      errs()_<<"\n optype is ::"<<Operand->getSCEVType();
//      if (Operand->getSCEVType() == scUMaxExpr) 
//          errs() <<"\n umax expr is ::"<< SE.getUMaxExpr(Operands); 
//    }
//  */
//    /*
//    const SCEV *V =  UB  ;
//    while (const SCEVCastExpr *C = dyn_cast<SCEVCastExpr>(V))
//        V = C->getOperand();
//    errs() <<"\n scev::"<<*V;
//    for (unsigned Op = 0, Ops = V->getNumOperands(); Op < Ops; Op++)  {
//      const SCEV *Operand = V->getOperand(Op);
//      errs() <<"\n operand::"<< *Operand;
//
//    }*/
//  
//}
//bool AnalyzeThisLoop(Loop *L, AliasAnalysis *AA,
//                                        LoopInfo *LI, DominatorTree *DT,
//                                        TargetLibraryInfo *TLI,
//                                        ScalarEvolution *SE, bool DeleteAST) {
//  bool Changed = false;
//
//  assert(L->isLCSSAForm(*DT) && "Loop is not in LCSSA form.");
//
//  errs() << "\n Starting Loop Stride Analysis for loop \n"<<*L;
//  runStrideComputation(L,AA, LI, DT, TLI, SE );
//  return false;
//
//  //AliasSetTracker *CurAST = collectAliasInfoForLoop(L, LI, AA);
//
//  // Get the preheader block to move instructions into...
//  BasicBlock *Preheader = L->getLoopPreheader();
//
//
//  // We want to visit all of the instructions in this loop... that are not parts
//  // of our subloops (they have already had their invariants hoisted out of
//  // their loop, into this loop, so there is no need to process the BODIES of
//  // the subloops).
//  //
//  // Traverse the body of the loop in depth first order on the dominator tree so
//  // that we are guaranteed to see definitions before we see uses.  This allows
//  // us to sink instructions in one pass, without iteration.  After sinking
//  // instructions, we perform another pass to hoist them out of the loop.
//  //
//    Changed |= sinkRegion(DT->getNode(L->getHeader()), AA, LI, DT, TLI, L);
//    //                      CurAST, &SafetyInfo);
//  
//
//  return Changed;
//}
//
///// Walk the specified region of the CFG (defined by all blocks dominated by
///// the specified block, and that are in the current loop) in reverse depth
///// first order w.r.t the DominatorTree.  This allows us to visit uses before
///// definitions, allowing us to sink a loop body in one pass without iteration.
/////
//bool sinkRegion(DomTreeNode *N, AliasAnalysis *AA, LoopInfo *LI,
//                      DominatorTree *DT, TargetLibraryInfo *TLI, Loop *CurLoop){
//
//  // Verify inputs.
//  assert(N != nullptr && AA != nullptr && LI != nullptr && DT != nullptr &&
//         CurLoop != nullptr  &&
//         "Unexpected input to sinkRegion");
//
//      //errs() << "inside sinkregion             ";
//  BasicBlock *BB = N->getBlock();
//  BasicBlock *H = BB;
//  // If this subregion is not in the top level loop at all, exit.
//  if (!CurLoop->contains(BB))
//    return false;
//
//  // We are processing blocks in reverse dfo, so process children first.
//  bool Changed = false;
//  for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; I++)
//        {
////  for (BasicBlock::iterator II = BB->end(); II != BB->begin();) {
//  //  Instruction &I = *--II;
//      errs() << "\n instruction :: " << *I ;
//      int num_ops = I->getNumOperands() -1;
//      errs() << " \n Num operands are ::"<<num_ops;
//      for (int i=0;i<num_ops;i++) {
//        errs()<<"\n operand is ::"<< *(I->getOperand(i));
//      }
//
//  }
//  BasicBlock *Incoming = nullptr, *Backedge = nullptr;
//  pred_iterator PI = pred_begin(H);
//  assert(PI != pred_end(H) &&
//         "Loop must have at least one backedge!");
//  Backedge = *PI++;
//  if (PI == pred_end(H)) return false  ;  // dead loop
//  Incoming = *PI++;
//  if (PI != pred_end(H)) return false  ;  // multiple backedges?
//
//  if (CurLoop->contains(Incoming)) {
//    if (CurLoop->contains(Backedge))
//      return false  ;
//    std::swap(Incoming, Backedge);
//  } else if (!CurLoop->contains(Backedge))
//    return false  ;
//
//  // Loop over all of the PHI nodes, looking for a canonical indvar.
//  for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
//	errs() << "\n Looping over phi nodes::"<<*I;
//    PHINode *PN = cast<PHINode>(I);
//    if (ConstantInt *CI =
//        dyn_cast<ConstantInt>(PN->getIncomingValueForBlock(Incoming)))
//      if (CI->isNullValue())
//        if (Instruction *Inc =
//            dyn_cast<Instruction>(PN->getIncomingValueForBlock(Backedge)))
//          if (Inc->getOpcode() == Instruction::Add &&
//                Inc->getOperand(0) == PN)
//            if (ConstantInt *CI = dyn_cast<ConstantInt>(Inc->getOperand(1)))
//              if (CI->equalsInt(1))
//                return false;
//  }
//  return Changed;
//}
//};
//}
//
//char MyLoopInfo::ID = 0;
//static RegisterPass<MyLoopInfo>
//Z("myLoopInfo", "Get Loop Info pass by Hello World ");
//
//
//
//
//
//STATISTIC(NumLoopNests, "Number of loop nests");
//STATISTIC(NumPerfectLoopNests, "Number of perfect loop nests");
//STATISTIC(NumIndependentMemOps, "Number of independent memory operations");
//STATISTIC(NumAmbiguousDependentMemOps, "Number of ambiguous dependent memory operations");
//STATISTIC(NumDirectionalDependentMemOps, "Number of directional dependent memory operations");
//STATISTIC(NumInterestingLoops, "Number of loops with a nontrivial direction matrix");
//
//namespace CS1745
//{
//
///* A single dependence */
//struct DependenceDirection
//{
//	char direction; // <,=,>, or *
//	int distance; //if exists, nonzero
//	
//	DependenceDirection(): direction('*'), distance(0) {}
//};
//
///*
// A class that represents a dependence matrix for a loop.  This is the union
// of all valid direction vectors of all dependences.
// */
//class DependenceMatrix
//{
//	//implement, feel free to change any data structures
//public:
//	DependenceMatrix();
//	DependenceMatrix(int n);
//	void add(const std::vector<DependenceDirection>& vec);
//	//more ?
//	void clear();	
//	void print(	std::ostream& out);
//	bool isTrivial(); //return true if empty (no dependence) or full (all dependencies)
//};
//
//class LoopDependence : public LoopPass
//{
//	std::ofstream file;
//public:
//	static char ID;
//
//	LoopDependence() : 
//		LoopPass(ID)
//	{
//		std::string name = "DEPINFO";
//	}
//
//	~LoopDependence()
//	{
//	}
//
//	virtual bool runOnLoop(Loop *L, LPPassManager &LPM);
//
//	virtual void getAnalysisUsage(AnalysisUsage &AU) const
//	{
//		AU.setPreservesAll();	// We don't modify the program, so we preserve all analyses
//		/*AU.addRequiredID(LoopSimplifyID);
//		AU.addRequired<LoopInfo>();
//		AU.addRequiredTransitive<AliasAnalysis>();
//		AU.addPreserved<AliasAnalysis>();*/
//	}
//
//private:
//	// Various analyses that we use...
//	AliasAnalysis *AA; // Current AliasAnalysis information
//	LoopInfo *LI; // Current LoopInfo
//
//
//};
//
//
//
//// Compute the dependence matrix of a loop.  Only consider perfectly
//// nested, single block loops with easily analyzed array accesses.
//bool LoopDependence::runOnLoop(Loop *L, LPPassManager &LPM)
//{
//      errs() << "Hello We called runonloop :: \n" ;
//
//
//	//now check that these loops are perfectly nested inside one another
//	BasicBlock *body;
//
//	
//	//go through the basic block and make sure only loads and stores
//	//access memory
//	for (BasicBlock::iterator I = body->begin(), E = body->end(); I != E; I++)
//	{
//		switch (I->getOpcode())
//		{
//			case Instruction::Invoke:
//			case Instruction::VAArg:
//			case Instruction::Call:
//				return false; //can't handle these		
//		}
//	}
//	
//	return false;
//}
//
//
//char LoopDependence::ID = 0;
//RegisterPass<LoopDependence> A("loop-dep", "Loop Dependence");
//}
/*
    enum stride_info_op_type {ADD, MULTIPLY, DIVIDE, POINTER_DEREFERENCE,INVALID }
    class strideInfo {
        unsigned int memArgument_num;
        class  expression_nodeType {
            int arg_num;
            GlobalVariable *globalVar ;//CAN ALSO BE A CONSTNAT
            bool isFunc_arg;
            stride_info_op_type operation;
            public:
            expression_nodeType() {
                arg_num = -1;
                globalVar = NULL;
                isFunc_arg = false;
                operation = INVALID;
            }
            expression_nodeType(const expression_nodeType &t) :
            arg_num(t.arg_num),  globalVar(t.globalVar), isFunc_arg(t.isFunc_arg), operation(t.operation);
            void set_arg_num(int n) { arg_num = n; isFunc_arg = 1;}
        };
        std::list<expression_nodeType> strideComputationExpression;
        public:
        strideInfo(int mem_argument ){
            memArgument_num = mem_argument;
        }
        void set_Expr_node(bool is_arg, int arg_num, GlobalVariable* gv=NULL,int op=-1 ){
            expression_nodeType t_node;
            t_node.isFunc_arg = is_arg;
            if (is_arg)
            t_node.arg_num  = arg_num;
            t_node.globalVar = gv;
            t_node.operation = op;
            strideComputationExpression.push_back(t_node ) ;
        }
        void print() {
            std::list<expression_nodeType>::iterator it;
            std::cout<<"\n Mem argument is::"<<memArgument_num;
            for (it=strideComputationExpression.begin(); it != strideComputationExpression.end() ; ++it ){
                std::cout<<"\n Variable::"<< (it->isFunc_arg ? it->arg_num :-1 ) <<"\t operation::  "<<it->operation;
            }
        }
    };
    */
    
    /*

    enum node_kind_type {ARGUMENT, GLOBAL, CONST, ADD, MULT, DIV, INVALID };
    class  expression_tree_node {
        friend class expression_tree;
        expression_tree_node *left;
        expression_tree_node *right;
        expression_tree_node * parent;
        node_kind_type nkind;
        int *argument_num;
        GlobalValue *globalVar;
        SCEVConstant *constInt;
        public:
        expression_tree_node(){
            left= NULL;
            right = NULL;
            parent = NULL;
            nkind = INVALID;
            argument_num = NULL;
            globalVar = NULL;
            constInt = NULL;
        }
        expression_tree_node *expression_tree_node_add_node(node_kind_type t,const void *val, bool is_left ){

            expression_tree_node *new_node = new expression_tree_node();
            new_node->nkind = t;
            new_node->parent = this;
            switch (t){
                case ARGUMENT: 
                    new_node->argument_num = new int      ;
                    new_node->argument_num[0] = *((int*)val)   ;
                    break;
                case GLOBAL:
                    new_node->globalVar = (GlobalValue *)val ;
                    break;
                case CONST:
                    new_node->constInt = (SCEVConstant *)val;
            }
            if (is_left )
                left = new_node;
            else
                right = new_node;
            return new_node;
        }
        node_kind_type getNodeKind() { return nkind;}
        expression_tree_node *getLeft() {return left;}
        expression_tree_node *getRight() {return right;}
        void * getValue() {

            switch (nkind){
                case ARGUMENT: 
                    return    argument_num ;
                    break;
                case GLOBAL:
                    return globalVar  ;
                    break;
                case CONST:
                    return    constInt ;
            }
            return NULL;
        }
    };
    class expression_tree {
        expression_tree_node *head;
        expression_tree_node *current;
        public:
        expression_tree () {
            head = NULL;
            current = NULL;
        }
        expression_tree_node *get_current () {return current;}
        expression_tree_node *get_head    () {return head   ;}
        void add_new_node(node_kind_type t,const void *val, bool is_left) {
            if (head == NULL){
                head = new expression_tree_node;
                current = head;
            }
            current = current->expression_tree_node_add_node(t, val, is_left );
        }
        void moveup() { current = current->parent;}
    };
    struct strideInfo {
        int mem_arg_num;
        expression_tree exp_compute_bound;
    };
  std::map<const Function *, strideInfo*> functionStride_map;

 */
 
//        Value *fix_block_stride_instr (Instruction *instr,IRBuilder<> &builder ) {
//            if (visit_done_set.find(instr )!= visit_done_set.end() ) return instr;
//            visit_done_set.insert(instr);
//
//            if (CallInst *callerI = dyn_cast<CallInst>(instr)) {//TODO add check here for  @llvm.nvvm.read.ptx.sreg.ctaid.x()
//                Function * calledFunc = callerI->getCalledFunction();
//                StringRef functionName = calledFunc->getName();
//                StringRef XblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.x" ) ;
//                StringRef YblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.y" ) ;
//                StringRef ZblockIdxString("llvm.nvvm.read.ptx.sreg.ctaid.z" ) ;
//                if (functionName.equals(XblockIdxString )){
//                    ConstantInt  *initializeIndex = llvm::ConstantInt::get(IntegerType::get (instr->getContext(), 32),
//                            get_init_const_value());// llvm::APInt(/*nbits*/32, value, /*bool*/is_signed));
//                    errs()<<"\n got a call with const::"<<*initializeIndex<<" \n Called functin with name::"<<calledFunc->getName();
//                    return initializeIndex;
//                } else if (functionName.equals(YblockIdxString )|| functionName.equals(ZblockIdxString )) { //TODO  handle the case when block stride is along Y or Z
//                    ConstantInt  *initializeIndex = llvm::ConstantInt::get(IntegerType::get (instr->getContext(), 32),0);// llvm::APInt(/*nbits*/32, value, /*bool*/is_signed));
//                    errs()<<"\n got a call with const::"<<*initializeIndex<<" \n Called function with name::"<<calledFunc->getName();
//                    return initializeIndex;
//                } else {
//                    return instr;
//                }
//            }else if (instr->isBinaryOp() ) {
//                errs()<<"\n got instruction with bin op::"<<*instr;
//                Value *op1 = instr->getOperand(0);
//                Value *op2 = instr->getOperand(1);
//                if (Instruction *parentInstr = dyn_cast<Instruction>(op1)) {
//                    if (parentInstr != instr )
//                        op1 = fix_block_stride_instr(parentInstr, builder);
//                }
//                if (Instruction *parentInstr = dyn_cast<Instruction>(op2)) {
//                    if (parentInstr != instr )
//                        op2 = fix_block_stride_instr(parentInstr, builder);
//                }
//                if (op1->getType() != op2->getType())
//                    op1 = builder.CreateSExt(op2, op1->getType());
//                Value* tmp = builder.CreateBinOp(Instruction::BinaryOps(instr->getOpcode()), op1, op2,
//                        "tmp_stride_compute");
//                return tmp;
//            }else if ( PHINode *index_phi = dyn_cast<PHINode>(instr)) {
//                Value *initial_index = index_phi->getIncomingValue(0 ); //TODO verify if this is always 0, or 1, by checking the basicblock
//                if (Instruction *index_instr = dyn_cast<Instruction>(initial_index)) {
//                    return fix_block_stride_instr(index_instr, builder);
//                }
//                return initial_index;
//            }else  {
//                if (instr->getNumOperands()==1 ) {
//                    Instruction *cloned_copy = instr->clone();
//                    Value *dupVal = instr->getOperand(0);
//                    if (Instruction *i = dyn_cast<Instruction>(dupVal ) ) {
//                        dupVal = fix_block_stride_instr(i, builder );
//                        cloned_copy->setOperand(0,dupVal );
//                        return builder.Insert(cloned_copy );
//                    }
//                }
//                return instr;
//            }
//        }
//        void getPrintfFunction(Module *mod) {
//            thisMod = mod;
//            printfFunction =dyn_cast<Function>( mod->getOrInsertFunction("printf",
//                        FunctionType::get(IntegerType::getInt32Ty(mod->getContext()),
//                            PointerType::get(Type::getInt8Ty(mod->getContext()), 0), true /*
//                                                                                             this is var arg func type*/) 
//                        ) );
//            if (printfFunction ) {
//                errs()<<"\n Hurray Got Printf::"<<printfFunction->getName();
//                printfStringMod = getStringRef( );
//            }
//
//            std::vector<Type*> ParamTypes;
//            ParamTypes.push_back( IntegerType::getInt64Ty(mod->getContext()));
//            wrapper_printfFunction =dyn_cast<Function>( mod->getOrInsertFunction("print_wrapper",
//                        FunctionType::get(IntegerType::getInt32Ty(mod->getContext()),
//                            ParamTypes , false) 
//                        ) );
//        }
                  //errs()<<"\n call instr::"<<*callinstr;

               // errs()<<"\n globalstring::"<<*printfStringMod<<"\n type is ::"<<*(printfStringMod->getType());
                //Constant
                //*GEP=ConstantExpr::getGetElementPtr(printfStringMod->getType(),printfStringMod,ConstantInt::get(Type::getInt64Ty(thisMod->getContext()),0));
                //std::vector<Constant*>(2,Constant::getNullValue(IntegerType::getInt64Ty(thisMod->getContext())))
                //Value *printfString = ConstantInt::get(Type::getInt32Ty(getGlobalContext()),1);
                //ArgsV.push_back(printfString );
                //
                //// get an instruction pointer
                //Instruction* ins_temp = &*i;
                ////create a call instruction and insert it before every instruction
                //CallInst *call_print =
                //CallInst::Create(call_print,paramArrayRef,"",ins_temp);
                //builder.CreateCall(printfFunction, ArgsV, "printfStrideCall");
        /*Constant* geti8StrVal(Module& M ) {
            char const* str = print_msg.c_str();
            LLVMContext& ctx = M.getContext();
            Constant* strConstant = ConstantDataArray::getString(thisMod->getContext(), str);
            GlobalVariable* GVStr =
                new GlobalVariable(M, strConstant->getType(), true,
                        GlobalValue::InternalLinkage, strConstant, "");
            Constant* zero = Constant::getNullValue(IntegerType::getInt32Ty(ctx));
            Constant* indices[] = {zero, zero};
            PointerType *PTy = dyn_cast<PointerType>(GVStr->getType());
            Constant* strVal = ConstantExpr::getGetElementPtr(PTy->getElementType(),GVStr, indices, true);
            return strVal;
        }*/
                    //std::vector<Value *> ArgsV;
                    //print_instr(computedStride);
                    //GlobalVariable *string_printf = getStringRef(print_msg );
                    //Constant* zero_i64 = Constant::getNullValue(IntegerType::getInt64Ty(thisMod->getContext()));
                    //ArrayRef< Value * > indices = {zero_i64,zero_i64};
                    //PointerType *pty = dyn_cast<PointerType>(string_printf->getType());
                    //GetElementPtrInst *gep_printf_string = GetElementPtrInst::Create( pty->getElementType(), string_printf,indices );
                    //if (debug_stride_pass) errs()<<"printf string load:: " <<*gep_printf_string;
                    //Value *printf_str_gep = builder.Insert(gep_printf_string,"tmp_blockstride_compute" );
                    //////ArgsV.push_back( geti8StrVal(*thisMod));
                    ////errs()<<"\n param type::"<<*computedStride->getType()<<"function wrapper::"<<*wrapper_printfFunction;
                    //Type *struct_ty = StructType::get(computedStride->getType(),nullptr );
                    ////Type *struct_ty = StructType::get(IntegerType::getInt32Ty(thisMod->getContext()),nullptr );
                    //if (debug_stride_pass) errs()<<"\n struct type:: "<<*struct_ty;
                    //Value * tmp_print_mem = builder.CreateAlloca(struct_ty ,nullptr, "tmp_stride_comp" );
                    //if (debug_stride_pass) errs()<<"\n alloca instr::"<<*tmp_print_mem<<"\n";

                    //Constant* zero_i32 = Constant::getNullValue(IntegerType::getInt32Ty(thisMod->getContext()));
                    //ArrayRef< Value * > indices2 = {zero_i64,zero_i32};
                    ////if (debug_stride_pass) errs()<<"\n Creating gep with pointer::"<<*tmp_print_mem<< "\n and indiex::"<<*indices[0]<<" and ::"<<*indices[1]<<"\n";
                    ////if (debug_stride_pass) errs()<<"\n pointer type::"<<*cast<PointerType>(tmp_print_mem->getType()->getScalarType())->getElementType()<<"\n"; 
                    //GetElementPtrInst *gepInstr = GetElementPtrInst::Create( struct_ty, tmp_print_mem,indices2 );
                    //Value *print_args_pointer = builder.Insert(gepInstr,"tmp_blockstride_compute" );// 	 builder.CreateGEP(tmp_print_mem,Constant::getNullValue(IntegerType::getInt32Ty(thisMod->getContext())));//indices);
                    //if (debug_stride_pass) errs()<<"\n printargspointer::"<<*print_args_pointer<<"\n ";
                    //Value *stored_arg = builder.CreateStore(computedStride,print_args_pointer );
                    //if (debug_stride_pass) errs()<<"store::"<<*stored_arg;
                    //Value *bitcast_arg = builder.CreateBitCast(tmp_print_mem,PointerType::get(IntegerType::getInt8Ty(thisMod->getContext()),0 ));
                    //ArgsV.push_back(printf_str_gep);  
                    //ArgsV.push_back(bitcast_arg);
                    ////if (debug_stride_pass) errs()<<"\n finally got bitcase as:"<<*bitcast_arg<<"\n and stored arg::"<<*stored_arg;
                    //Type *ptr_i8 = PointerType::get(Type::getInt8Ty(thisMod->getContext()), 0);
                    //llvm::Type *ArgTypes[] = { ptr_i8,ptr_i8 }	;
                    //Function *vprintfFunction =dyn_cast<Function>( thisMod->getOrInsertFunction("vprintf",
                    //            FunctionType::get(IntegerType::getInt32Ty(thisMod->getContext()),
                    //                ArgTypes,false /*
                    //                                  this is var arg func type*/) 
                    //            ) );
                    //if (vprintfFunction == nullptr ) {
                    //    if (debug_stride_pass) errs()<<"\n func def not found::";
                    //    return;
                    //}
                    //if (debug_stride_pass) errs()<<"\n vprintf::"<<*vprintfFunction;
                    //Value* callinstr = builder.CreateCall(vprintfFunction,ArgsV  );
