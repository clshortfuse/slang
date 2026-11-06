#include "slang-emit-nx2.h"

#include "core/slang-string-util.h"
#include "slang-diagnostics.h"
#include "slang-ir-dce.h"
#include "slang-ir-inline.h"
#include "slang-ir-insts.h"
#include "slang-ir-restructure.h"
#include "slang-ir-sccp.h"
#include "slang-ir-simplify-cfg.h"
#include "slang-ir-util.h"
#include "slang-parameter-binding.h"

namespace Slang
{
// Return whether an instruction may be evaluated on both sides of an NX2 conditional.
// For example, a floating-point multiply can be selected after evaluation, but a guarded
// division, load, or call must remain in its original control-flow arm.
static bool canSpeculateNX2ConditionalInst(IRInst* inst)
{
    auto type = inst->getDataType();
    if (auto vector = as<IRVectorType>(type))
        type = vector->getElementType();
    return type && type->getOp() == kIROp_FloatType && inst->getOp() == kIROp_Mul;
}

// Return whether an instruction is an equality comparison that can select a constant integer mode.
static bool isNX2IntegerComparison(IRInst* inst)
{
    if (inst->getOp() != kIROp_Eql || inst->getOperandCount() != 2)
        return false;
    auto type = inst->getOperand(0)->getDataType();
    return type && type == inst->getOperand(1)->getDataType() &&
           (type->getOp() == kIROp_IntType || type->getOp() == kIROp_UIntType);
}

bool inlineNX2LeafCalls(IRFunc* function, TargetProgram* targetProgram)
{
    bool changed = false;
    for (;;)
    {
        IRCall* candidate = nullptr;
        bool foldControlFlow = false;
        for (auto block : function->getBlocks())
        {
            for (auto inst : block->getOrdinaryInsts())
            {
                auto call = as<IRCall>(inst);
                auto function = call ? as<IRFunc>(call->getCallee()) : nullptr;
                auto body = function ? function->getFirstBlock() : nullptr;
                if (!body)
                    continue;
                bool straightLine = !body->getNextBlock() && as<IRReturn>(body->getTerminator());
                if (as<IRGenericAsm>(body->getTerminator()))
                    continue;
                bool leaf = true;
                for (auto calleeBlock : function->getBlocks())
                {
                    for (auto bodyInst : calleeBlock->getOrdinaryInsts())
                    {
                        if (auto innerCall = as<IRCall>(bodyInst))
                        {
                            auto innerFunc = as<IRFunc>(innerCall->getCallee());
                            auto innerBlock = innerFunc ? innerFunc->getFirstBlock() : nullptr;
                            if (!innerBlock || innerBlock->getNextBlock() ||
                                !as<IRGenericAsm>(innerBlock->getTerminator()))
                                leaf = false;
                        }
                    }
                }
                if (leaf)
                {
                    candidate = call;
                    foldControlFlow = !straightLine;
                    break;
                }
            }
            if (candidate)
                break;
        }
        if (!candidate || !inlineCall(candidate))
            return changed;
        changed = true;
        if (foldControlFlow)
        {
            for (auto block : function->getBlocks())
            {
                if (auto conditional = as<IRIfElse>(block->getTerminator()))
                {
                    auto comparison = conditional->getCondition();
                    if (isNX2IntegerComparison(comparison))
                    {
                        auto left = as<IRIntLit>(comparison->getOperand(0));
                        auto right = as<IRIntLit>(comparison->getOperand(1));
                        if (left && right)
                            tryConstantFoldInst(function->getModule(), targetProgram, comparison);
                    }
                    if (auto condition = as<IRBoolLit>(conditional->getCondition()))
                    {
                        IRBuilder builder(conditional);
                        builder.setInsertBefore(conditional);
                        builder.emitBranch(
                            condition->getValue() ? conditional->getTrueBlock()
                                                  : conditional->getFalseBlock());
                        conditional->removeAndDeallocate();
                    }
                }
            }
            eliminateDeadCode(function);
            simplifyCFG(function, CFGSimplificationOptions{true, false});
            eliminateDeadCode(function);
            simplifyCFG(function, CFGSimplificationOptions::getFast());
        }
        else
            simplifyCFG(function, CFGSimplificationOptions::getFast());
    }
}

bool lowerNX2SpeculatableConditionals(IRFunc* function)
{
    bool changed = false;
    for (auto block : function->getBlocks())
    {
        auto conditional = as<IRIfElse>(block->getTerminator());
        if (!conditional)
            continue;
        auto trueBlock = conditional->getTrueBlock();
        auto falseBlock = conditional->getFalseBlock();
        auto afterBlock = conditional->getAfterBlock();
        if (trueBlock == falseBlock || trueBlock->getFirstParam() || falseBlock->getFirstParam() ||
            trueBlock->getPredecessors().getCount() != 1 ||
            falseBlock->getPredecessors().getCount() != 1)
            continue;
        auto trueBranch = as<IRUnconditionalBranch>(trueBlock->getTerminator());
        auto falseBranch = as<IRUnconditionalBranch>(falseBlock->getTerminator());
        auto trueReturn = as<IRReturn>(trueBlock->getTerminator());
        auto falseReturn = as<IRReturn>(falseBlock->getTerminator());
        bool returns = trueReturn && falseReturn && trueReturn->getOperandCount() == 1 &&
                       falseReturn->getOperandCount() == 1 &&
                       trueReturn->getVal()->getDataType() == falseReturn->getVal()->getDataType();
        bool branches = trueBranch && falseBranch && trueBlock != afterBlock &&
                        falseBlock != afterBlock && !trueBlock->hasMoreThanOneUse() &&
                        !falseBlock->hasMoreThanOneUse() &&
                        trueBranch->getTargetBlock() == afterBlock &&
                        falseBranch->getTargetBlock() == afterBlock &&
                        trueBranch->getArgCount() == falseBranch->getArgCount();
        if (!returns && !branches)
            continue;
        bool safe = true;
        for (auto arm : {trueBlock, falseBlock})
        {
            for (auto inst : arm->getOrdinaryInsts())
            {
                if (inst != arm->getTerminator() && !canSpeculateNX2ConditionalInst(inst))
                    safe = false;
            }
        }
        if (!safe)
            continue;
        for (auto arm : {trueBlock, falseBlock})
        {
            for (auto inst = arm->getFirstOrdinaryInst(); inst != arm->getTerminator();)
            {
                auto next = inst->getNextInst();
                inst->insertBefore(conditional);
                inst = next;
            }
        }
        List<IRInst*> arguments;
        IRBuilder builder(conditional);
        builder.setInsertBefore(conditional);
        UInt count = returns ? 1 : trueBranch->getArgCount();
        for (UInt i = 0; i < count; ++i)
        {
            IRInst* operands[] = {
                conditional->getCondition(),
                returns ? trueReturn->getVal() : trueBranch->getArg(i),
                returns ? falseReturn->getVal() : falseBranch->getArg(i)};
            arguments.add(
                builder.emitIntrinsicInst(operands[1]->getDataType(), kIROp_Select, 3, operands));
        }
        if (returns)
            builder.emitReturn(arguments[0]);
        else
            builder.emitBranch(afterBlock, arguments.getCount(), arguments.getBuffer());
        conditional->removeAndDeallocate();
        changed = true;
    }
    return changed;
}

bool lowerNX2AcyclicLoops(IRFunc* function)
{
    List<IRBlock*> blocks;
    List<List<Index>> successors;
    Dictionary<IRBlock*, Index> indices;
    auto first = function->getFirstBlock();
    if (!first)
        return false;
    blocks.add(first);
    indices.add(first, 0);
    bool hasLoop = false;
    Index returnCount = 0;
    for (Index index = 0; index < blocks.getCount(); ++index)
    {
        auto terminator = blocks[index]->getTerminator();
        if (!terminator)
            return false;
        List<IRBlock*> targets;
        if (auto conditional = as<IRIfElse>(terminator))
        {
            targets.add(conditional->getTrueBlock());
            targets.add(conditional->getFalseBlock());
        }
        else if (auto branch = as<IRUnconditionalBranch>(terminator))
        {
            if (branch->getArgCount())
                return false;
            targets.add(branch->getTargetBlock());
            hasLoop |= as<IRLoop>(terminator) != nullptr;
        }
        else if (as<IRReturn>(terminator))
            ++returnCount;
        else
            return false;
        List<Index> edges;
        for (auto target : targets)
        {
            auto found = indices.tryGetValue(target);
            if (!found)
            {
                Index next = blocks.getCount();
                blocks.add(target);
                indices.add(target, next);
                edges.add(next);
            }
            else
                edges.add(*found);
        }
        successors.add(_Move(edges));
    }
    if (!hasLoop || returnCount != 1)
        return false;

    List<Index> incoming;
    incoming.setCount(blocks.getCount());
    for (auto& count : incoming)
        count = 0;
    for (const auto& edges : successors)
        for (Index target : edges)
            ++incoming[target];
    List<Index> order;
    for (Index index = 0; index < incoming.getCount(); ++index)
        if (!incoming[index])
            order.add(index);
    for (Index position = 0; position < order.getCount(); ++position)
    {
        for (Index target : successors[order[position]])
            if (--incoming[target] == 0)
                order.add(target);
    }
    if (order.getCount() != blocks.getCount())
        return false;

    List<HashSet<Index>> postdominators;
    postdominators.setCount(blocks.getCount());
    for (Index position = order.getCount(); position-- > 0;)
    {
        Index index = order[position];
        auto& set = postdominators[index];
        set.add(index);
        if (successors[index].getCount())
        {
            for (Index candidate : postdominators[successors[index][0]])
            {
                bool common = true;
                for (Index target : successors[index])
                    common &= postdominators[target].contains(candidate);
                if (common)
                    set.add(candidate);
            }
        }
    }
    List<IRBlock*> joins;
    joins.setCount(blocks.getCount());
    for (Index index = 0; index < blocks.getCount(); ++index)
    {
        joins[index] = nullptr;
        if (!as<IRIfElse>(blocks[index]->getTerminator()))
            continue;
        Index closest = -1;
        for (Index candidate : postdominators[index])
        {
            if (candidate != index && (closest < 0 || postdominators[candidate].getCount() >
                                                          postdominators[closest].getCount()))
                closest = candidate;
        }
        if (closest < 0)
            return false;
        joins[index] = blocks[closest];
    }
    for (Index index = 0; index < blocks.getCount(); ++index)
    {
        auto terminator = blocks[index]->getTerminator();
        if (auto conditional = as<IRIfElse>(terminator))
            conditional->afterBlock.set(joins[index]);
        else if (auto loop = as<IRLoop>(terminator))
        {
            IRBuilder builder(loop);
            builder.setInsertBefore(loop);
            builder.emitBranch(loop->getTargetBlock());
            loop->removeAndDeallocate();
        }
    }
    function->getModule()->invalidateAnalysisForInst(function);
    return true;
}

bool lowerNX2MatrixOperations(IRFunc* entryPoint)
{
    List<IRCall*> calls;
    for (auto block = entryPoint->getFirstBlock(); block; block = block->getNextBlock())
    {
        for (auto inst : block->getOrdinaryInsts())
        {
            auto call = as<IRCall>(inst);
            auto function = call ? as<IRFunc>(call->getOperand(0)) : nullptr;
            auto body = function ? function->getFirstBlock() : nullptr;
            auto terminator = body ? body->getTerminator() : nullptr;
            auto text = terminator && terminator->getOp() == kIROp_GenericAsm
                            ? as<IRStringLit>(terminator->getOperand(0))
                            : nullptr;
            if (text && (text->getStringSlice() == toSlice("nx2_matrix_vector_mul") ||
                         text->getStringSlice() == toSlice("nx2_matrix_matrix_mul") ||
                         text->getStringSlice() == toSlice("nx2_matrix_transpose")))
                calls.add(call);
        }
    }

    bool changed = false;
    for (auto call : calls)
    {
        if (call->getArgCount() == 1)
        {
            auto inputType = as<IRMatrixType>(call->getArg(0)->getDataType());
            auto resultType = as<IRMatrixType>(call->getDataType());
            auto rows = inputType ? as<IRIntLit>(inputType->getRowCount()) : nullptr;
            auto columns = inputType ? as<IRIntLit>(inputType->getColumnCount()) : nullptr;
            if (!inputType || !resultType ||
                inputType->getElementType()->getOp() != kIROp_FloatType || !rows || !columns ||
                rows->getValue() < 1 || rows->getValue() > 4 || columns->getValue() < 1 ||
                columns->getValue() > 4)
                continue;
            IRBuilder builder(call);
            builder.setInsertBefore(call);
            List<IRInst*> elements;
            for (IRIntegerValue row = 0; row < columns->getValue(); ++row)
                for (IRIntegerValue column = 0; column < rows->getValue(); ++column)
                    elements.add(builder.emitElementExtract(
                        builder.emitElementExtract(call->getArg(0), column),
                        row));
            auto result =
                builder.emitMakeMatrix(resultType, UInt(elements.getCount()), elements.getBuffer());
            call->replaceUsesWith(result);
            call->removeAndDeallocate();
            changed = true;
            continue;
        }
        if (call->getArgCount() != 2)
            continue;
        auto matrixType = as<IRMatrixType>(call->getArg(0)->getDataType());
        auto rightMatrixType = as<IRMatrixType>(call->getArg(1)->getDataType());
        auto resultMatrixType = as<IRMatrixType>(call->getDataType());
        if (matrixType && rightMatrixType && resultMatrixType &&
            matrixType->getElementType()->getOp() == kIROp_FloatType)
        {
            auto rows = as<IRIntLit>(matrixType->getRowCount());
            auto inner = as<IRIntLit>(matrixType->getColumnCount());
            auto columns = as<IRIntLit>(rightMatrixType->getColumnCount());
            if (!rows || !inner || !columns || rows->getValue() < 1 || rows->getValue() > 4 ||
                inner->getValue() < 1 || inner->getValue() > 4 || columns->getValue() < 1 ||
                columns->getValue() > 4)
                continue;
            IRBuilder builder(call);
            builder.setInsertBefore(call);
            List<IRInst*> components;
            for (IRIntegerValue row = 0; row < rows->getValue(); ++row)
            {
                auto leftRow = builder.emitElementExtract(call->getArg(0), row);
                for (IRIntegerValue column = 0; column < columns->getValue(); ++column)
                {
                    IRInst* sum = builder.getFloatValue(matrixType->getElementType(), 0.0);
                    for (IRIntegerValue index = 0; index < inner->getValue(); ++index)
                    {
                        auto left = builder.emitElementExtract(leftRow, index);
                        auto rightRow = builder.emitElementExtract(call->getArg(1), index);
                        auto right = builder.emitElementExtract(rightRow, column);
                        auto product = builder.emitMul(matrixType->getElementType(), left, right);
                        sum = builder.emitAdd(matrixType->getElementType(), sum, product);
                    }
                    components.add(sum);
                }
            }
            auto result = builder.emitMakeMatrix(
                resultMatrixType,
                UInt(components.getCount()),
                components.getBuffer());
            call->replaceUsesWith(result);
            call->removeAndDeallocate();
            changed = true;
            continue;
        }
        auto vectorType = as<IRVectorType>(call->getArg(1)->getDataType());
        auto resultType = as<IRVectorType>(call->getDataType());
        if (!matrixType || !vectorType || !resultType ||
            matrixType->getElementType()->getOp() != kIROp_FloatType)
            continue;
        auto rows = as<IRIntLit>(matrixType->getRowCount());
        auto columns = as<IRIntLit>(matrixType->getColumnCount());
        if (!rows || !columns || rows->getValue() < 1 || rows->getValue() > 4 ||
            columns->getValue() < 1 || columns->getValue() > 4)
            continue;

        IRBuilder builder(call);
        builder.setInsertBefore(call);
        List<IRInst*> components;
        for (IRIntegerValue row = 0; row < rows->getValue(); ++row)
        {
            auto matrixRow = builder.emitElementExtract(call->getArg(0), row);
            IRInst* sum = builder.getFloatValue(matrixType->getElementType(), 0.0);
            for (IRIntegerValue column = 0; column < columns->getValue(); ++column)
            {
                auto left = builder.emitElementExtract(matrixRow, column);
                auto index = builder.getIntValue(column);
                auto right =
                    builder.emitSwizzle(matrixType->getElementType(), call->getArg(1), 1, &index);
                auto product = builder.emitMul(matrixType->getElementType(), left, right);
                sum = builder.emitAdd(matrixType->getElementType(), sum, product);
            }
            components.add(sum);
        }
        auto result = builder.emitMakeVector(resultType, components);
        call->replaceUsesWith(result);
        call->removeAndDeallocate();
        changed = true;
    }
    return changed;
}

// Split mutable struct locals into field locals, preserving whole-value loads and stores.
// For example, writes to `state.color` and `state.value` remain independent across branches.
bool lowerNX2LocalStructs(IRFunc* entryPoint)
{
    List<IRVar*> candidates;
    for (auto block : entryPoint->getBlocks())
        for (auto inst : block->getOrdinaryInsts())
            if (auto var = as<IRVar>(inst))
                if (auto pointer = as<IRPtrTypeBase>(var->getDataType()))
                    if (as<IRStructType>(pointer->getValueType()))
                        candidates.add(var);

    bool changed = false;
    for (Index candidateIndex = 0; candidateIndex < candidates.getCount(); ++candidateIndex)
    {
        auto var = candidates[candidateIndex];
        auto structType = as<IRStructType>(as<IRPtrTypeBase>(var->getDataType())->getValueType());
        bool supported = true;
        for (auto use = var->firstUse; use; use = use->nextUse)
        {
            auto user = use->getUser();
            if (auto address = as<IRFieldAddress>(user))
                supported &= address->getBase() == var;
            else if (auto load = as<IRLoad>(user))
                supported &= load->getPtr() == var;
            else if (auto store = as<IRStore>(user))
                supported &= store->getPtr() == var;
            else
                supported = false;
        }
        if (!supported)
            continue;

        IRBuilder builder(var);
        builder.setInsertBefore(var);
        Dictionary<IRInst*, IRVar*> fields;
        for (auto field : structType->getFields())
        {
            auto fieldVar = builder.emitVar(field->getFieldType());
            fields.add(field->getKey(), fieldVar);
            if (as<IRStructType>(field->getFieldType()))
                candidates.add(fieldVar);
        }
        while (var->firstUse)
        {
            auto user = var->firstUse->getUser();
            builder.setInsertBefore(user);
            if (auto address = as<IRFieldAddress>(user))
            {
                auto field = fields.tryGetValue(address->getField());
                SLANG_RELEASE_ASSERT(field);
                address->replaceUsesWith(*field);
                address->removeAndDeallocate();
            }
            else if (auto load = as<IRLoad>(user))
            {
                List<IRInst*> values;
                for (auto field : structType->getFields())
                    values.add(builder.emitLoad(fields[field->getKey()]));
                auto value = builder.emitMakeStruct(structType, values);
                load->replaceUsesWith(value);
                load->removeAndDeallocate();
            }
            else
            {
                auto store = cast<IRStore>(user);
                for (auto field : structType->getFields())
                    builder.emitStore(
                        fields[field->getKey()],
                        builder.emitFieldExtract(
                            field->getFieldType(),
                            store->getVal(),
                            field->getKey()));
                store->removeAndDeallocate();
            }
        }
        var->removeAndDeallocate();
        changed = true;
    }
    return changed;
}

namespace
{
// The pinned nested-control-flow reference uses registers through R124. This
// smaller allocation budget is a backend limit, not a hardware maximum.
constexpr UInt kNX2AllocatableRegisterCount = 125;
// The pinned deep-control-flow capture uses nested barriers B0 through B7.
constexpr UInt kNX2ReconvergenceBarrierCount = 8;

enum class NX2Interface
{
    PerspectiveTexture,
    ScreenTexture
};

// Return the native TEXCOORD slot, or -1 when the semantic is outside this interface.
// For example, TEXCOORD1.x occupies a[0x90] in the four-component slot layout.
Int getNX2VaryingSlot(IRParam* param)
{
    auto decoration = param->findDecoration<IRSemanticDecoration>();
    if (!decoration)
        return -1;
    UnownedStringSlice name;
    UnownedStringSlice digits;
    splitNameAndIndex(decoration->getSemanticName(), name, digits);
    Int index = decoration->getEffectiveSemanticIndex();
    if (name != toSlice("TEXCOORD") ||
        (digits.getLength() && SLANG_FAILED(StringUtil::parseInt(digits, index))) || index < 0 ||
        index >= 32)
        return -1;
    return index;
}

struct NX2LiveInterval
{
    Index start;
    Index end;
    UInt virtualRegister;
    UInt physicalRegister = 255;
    Index preferredSource = -1;
};

struct NX2RegisterToken
{
    Index start;
    Index end;
    UInt number;
    Index interval = -1;
};

struct NX2NativeLine
{
    String text;
    List<NX2RegisterToken> registers;
};

struct NX2ControlFlowLine
{
    NX2NativeLine native;
    List<Index> successors;
    HashSet<UInt> reads;
    HashSet<UInt> writes;
    HashSet<UInt> liveIn;
    HashSet<UInt> liveOut;
};

// Allocate conditional-path temporaries from CFG liveness without reordering instructions.
// Values assigned in both arms, for example, retain one register at their merge.
SlangResult allocateNX2ConditionalRegisters(
    const String& input,
    UInt nextRegister,
    UInt outputCount,
    DiagnosticSink* sink,
    StringBuilder* output)
{
    List<NX2ControlFlowLine> lines;
    Dictionary<String, Index> labels;
    for (Index start = 0; start < input.getLength();)
    {
        Index end = start;
        while (end < input.getLength() && input[end] != '\n')
            ++end;
        NX2ControlFlowLine line;
        line.native.text = input.subString(start, end - start);
        start = end + 1;
        auto text = line.native.text.getUnownedSlice();
        if (text.endsWith(toSlice(":")))
            labels.add(line.native.text.subString(0, text.getLength() - 1), lines.getCount());
        if (!text.startsWith(toSlice("//")))
        {
            for (Index offset = 0; offset < text.getLength(); ++offset)
            {
                if (text[offset] != 'R' || offset + 1 == text.getLength() ||
                    text[offset + 1] < '0' || text[offset + 1] > '9')
                    continue;
                Index last = offset + 1;
                UInt number = 0;
                while (last < text.getLength() && text[last] >= '0' && text[last] <= '9')
                    number = number * 10 + UInt(text[last++] - '0');
                line.native.registers.add({offset, last, number});
                offset = last - 1;
            }
        }
        bool predicate = text.startsWith(toSlice("FSETP.")) || text.startsWith(toSlice("ISETP."));
        bool texture = text.startsWith(toSlice("TEX.SCR.NODEP "));
        if (texture)
        {
            if (line.native.registers.getCount() != 4 || line.native.registers[0].number != 2 ||
                line.native.registers[1].number != 0 || line.native.registers[2].number != 8 ||
                line.native.registers[3].number != 9)
            {
                sink->diagnose(
                    Diagnostics::Unimplemented{
                        .feature =
                            "NX2 conditional texture operands require the fixed register banks",
                        .location = SourceLoc()});
                return SLANG_FAIL;
            }
            line.reads.add(8);
            line.reads.add(9);
            for (UInt number = 0; number < 4; ++number)
                line.writes.add(number);
        }
        else if (text == toSlice("EXIT;"))
        {
            for (UInt number = 0; number < outputCount; ++number)
                line.reads.add(number);
        }
        else
        {
            for (Index index = 0; index < line.native.registers.getCount(); ++index)
            {
                UInt number = line.native.registers[index].number;
                if (!predicate && index == 0)
                    line.writes.add(number);
                else
                    line.reads.add(number);
            }
        }
        lines.add(_Move(line));
    }
    for (Index index = 0; index < lines.getCount(); ++index)
    {
        auto text = lines[index].native.text.getUnownedSlice();
        bool unconditional = text.startsWith(toSlice("BRA "));
        bool conditionalNot = text.startsWith(toSlice("@!P0 BRA "));
        bool conditional = conditionalNot || text.startsWith(toSlice("@P0 BRA "));
        if (unconditional || conditional)
        {
            Index prefix = unconditional ? 4 : conditionalNot ? 9 : 8;
            String label =
                lines[index].native.text.subString(prefix, text.getLength() - prefix - 1);
            auto target = labels.tryGetValue(label);
            if (!target)
            {
                sink->diagnose(
                    Diagnostics::Unimplemented{
                        .feature = "NX2 conditional branch target is undefined",
                        .location = SourceLoc()});
                return SLANG_FAIL;
            }
            lines[index].successors.add(*target);
        }
        if (!unconditional && text != toSlice("EXIT;") && index + 1 < lines.getCount())
            lines[index].successors.add(index + 1);
    }
    bool changed = true;
    while (changed)
    {
        changed = false;
        for (Index index = lines.getCount(); index-- > 0;)
        {
            auto& line = lines[index];
            for (Index successor : line.successors)
                for (UInt number : lines[successor].liveIn)
                    changed |= line.liveOut.add(number);
            for (UInt number : line.liveOut)
                if (!line.writes.contains(number))
                    changed |= line.liveIn.add(number);
            for (UInt number : line.reads)
                changed |= line.liveIn.add(number);
        }
    }
    List<HashSet<UInt>> interference;
    interference.setCount(nextRegister);
    for (const auto& line : lines)
    {
        for (UInt destination : line.writes)
        {
            for (UInt other : line.liveOut)
            {
                if (destination != other)
                {
                    interference[destination].add(other);
                    interference[other].add(destination);
                }
            }
        }
    }
    List<UInt> physical;
    physical.setCount(nextRegister);
    for (UInt number = 0; number < nextRegister; ++number)
        physical[number] = number < 11 ? number : UInt(255);
    for (UInt number = 11; number < nextRegister; ++number)
    {
        for (UInt candidate = 0; candidate < kNX2AllocatableRegisterCount; ++candidate)
        {
            bool available = true;
            for (UInt other : interference[number])
                if (physical[other] == candidate)
                    available = false;
            if (available)
            {
                physical[number] = candidate;
                break;
            }
        }
        if (physical[number] == 255)
        {
            sink->diagnose(
                Diagnostics::Unimplemented{
                    .feature = "NX2 conditional allocation exceeds 125 registers",
                    .location = SourceLoc()});
            return SLANG_FAIL;
        }
    }
    for (const auto& line : lines)
    {
        Index offset = 0;
        for (const auto& token : line.native.registers)
        {
            *output << line.native.text.subString(offset, token.start - offset) << "R"
                    << physical[token.number];
            offset = token.end;
        }
        *output << line.native.text.subString(offset, line.native.text.getLength() - offset)
                << "\n";
    }
    return SLANG_OK;
}

struct NX2ScheduledInstruction
{
    String text;
    List<Index> dependencies;
    Index priority = 0;
    bool emitted = false;
};

// Order independent work by modeled critical path, retaining all physical RAW/WAR/WAW edges.
// Priority weights are heuristics; completion barriers are generated and checked separately.
void scheduleNX2Lines(
    const List<NX2NativeLine>& lines,
    const List<NX2LiveInterval>& intervals,
    UInt outputCount,
    StringBuilder* output)
{
    List<NX2ScheduledInstruction> program;
    // The final slot represents P0 rather than a physical register.
    Index lastWrite[kNX2AllocatableRegisterCount + 1];
    List<Index> readers[kNX2AllocatableRegisterCount + 1];
    for (auto& value : lastWrite)
        value = -1;
    for (const auto& line : lines)
    {
        if (line.text.getLength() == 0 || line.text.getUnownedSlice().startsWith(toSlice("//")))
        {
            *output << line.text << "\n";
            continue;
        }
        NX2ScheduledInstruction instruction;
        StringBuilder rendered;
        List<UInt> registers;
        Index offset = 0;
        for (const auto& token : line.registers)
        {
            UInt number = intervals[token.interval].physicalRegister;
            rendered << line.text.subString(offset, token.start - offset) << "R" << number;
            registers.add(number);
            offset = token.end;
        }
        rendered << line.text.subString(offset, line.text.getLength() - offset);
        instruction.text = rendered.toString();
        auto text = instruction.text.getUnownedSlice();
        if (text.startsWith(toSlice("MOV ")) && registers.getCount() == 2 &&
            registers[0] == registers[1])
            continue;
        bool texture = text.startsWith(toSlice("TEX."));
        bool exit = text == toSlice("EXIT;");
        bool variable =
            texture || text.startsWith(toSlice("IPA.")) || text.startsWith(toSlice("MUFU."));
        instruction.priority = texture ? 32 : variable ? 8 : 4;
        List<UInt> reads;
        List<UInt> writes;
        if (exit)
        {
            for (UInt number = 0; number < outputCount; ++number)
                reads.add(number);
        }
        else if (texture)
        {
            reads.add(registers[2]);
            reads.add(registers[3]);
            for (UInt lane = 0; lane < 4; ++lane)
                writes.add(registers[1] + lane);
        }
        else if (text.startsWith(toSlice("CS2R ")))
        {
            SLANG_RELEASE_ASSERT(registers.getCount() == 1 && registers[0] % 2 == 0);
            writes.add(registers[0]);
            writes.add(registers[0] + 1);
        }
        else if (text.startsWith(toSlice("FSETP.")) || text.startsWith(toSlice("ISETP.")))
        {
            for (UInt number : registers)
                reads.add(number);
            writes.add(kNX2AllocatableRegisterCount);
        }
        else
        {
            writes.add(registers[0]);
            for (Index index = 1; index < registers.getCount(); ++index)
                reads.add(registers[index]);
            if (text.startsWith(toSlice("SEL ")) || text.startsWith(toSlice("FSEL ")))
                reads.add(kNX2AllocatableRegisterCount);
        }
        Index index = program.getCount();
        for (UInt number : reads)
        {
            SLANG_ASSERT(lastWrite[number] >= 0);
            instruction.dependencies.add(lastWrite[number]);
            readers[number].add(index);
        }
        for (UInt number : writes)
        {
            if (lastWrite[number] >= 0)
                instruction.dependencies.add(lastWrite[number]);
            for (Index reader : readers[number])
            {
                if (reader != index)
                    instruction.dependencies.add(reader);
            }
            readers[number].clear();
            lastWrite[number] = index;
        }
        if (exit)
        {
            for (Index previous = 0; previous < index; ++previous)
                instruction.dependencies.add(previous);
        }
        program.add(instruction);
    }
    for (Index index = program.getCount(); index-- > 0;)
    {
        Index successorPriority = 0;
        for (Index next = index + 1; next < program.getCount(); ++next)
        {
            for (Index dependency : program[next].dependencies)
            {
                if (dependency == index && program[next].priority > successorPriority)
                    successorPriority = program[next].priority;
            }
        }
        program[index].priority += successorPriority;
    }
    for (Index emitted = 0; emitted < program.getCount(); ++emitted)
    {
        Index selected = -1;
        for (Index index = 0; index < program.getCount(); ++index)
        {
            if (program[index].emitted)
                continue;
            bool ready = true;
            for (Index dependency : program[index].dependencies)
            {
                if (!program[dependency].emitted)
                    ready = false;
            }
            if (ready && (selected < 0 || program[index].priority > program[selected].priority))
                selected = index;
        }
        SLANG_RELEASE_ASSERT(selected >= 0);
        *output << program[selected].text << "\n";
        program[selected].emitted = true;
    }
}

// Allocate each native definition separately so read-before-write operands may share a register.
// Fixed intervals include future output writes, not just registers already assigned by the scan.
SlangResult allocateNX2Registers(
    const String& input,
    DiagnosticSink* sink,
    UInt outputCount,
    StringBuilder* output)
{
    List<NX2NativeLine> lines;
    List<NX2LiveInterval> intervals;
    Dictionary<UInt, Index> current;
    bool valid = true;
    Index instruction = 0;
    auto read = [&](UInt number, Index position)
    {
        auto currentInterval = current.tryGetValue(number);
        if (!currentInterval)
        {
            valid = false;
            return Index(-1);
        }
        intervals[*currentInterval].end = position;
        return *currentInterval;
    };
    auto write = [&](UInt number, Index position)
    {
        Index index = intervals.getCount();
        intervals.add({position, position, number, number < 11 ? number : UInt(255)});
        current.set(number, index);
        return index;
    };
    for (Index start = 0; start < input.getLength();)
    {
        Index end = start;
        while (end < input.getLength() && input[end] != '\n')
            ++end;
        NX2NativeLine line;
        line.text = input.subString(start, end - start);
        start = end + 1;
        auto text = line.text.getUnownedSlice();
        if (text.getLength() == 0 || text.startsWith(toSlice("//")))
        {
            lines.add(line);
            continue;
        }
        for (Index offset = 0; offset < text.getLength(); ++offset)
        {
            if (text[offset] != 'R' || offset + 1 == text.getLength() || text[offset + 1] < '0' ||
                text[offset + 1] > '9')
                continue;
            Index last = offset + 1;
            UInt number = 0;
            while (last < text.getLength() && text[last] >= '0' && text[last] <= '9')
                number = number * 10 + UInt(text[last++] - '0');
            line.registers.add({offset, last, number});
            offset = last - 1;
        }
        bool texture = text.startsWith(toSlice("TEX.SCR.NODEP "));
        bool exit = text == toSlice("EXIT;");
        if (exit)
        {
            for (UInt number = 0; number < outputCount; ++number)
                read(number, instruction * 2);
        }
        else if (texture)
        {
            if (line.registers.getCount() != 4 ||
                line.registers[0].number != line.registers[1].number + 2 ||
                line.registers[3].number != line.registers[2].number + 1)
                valid = false;
            if (valid)
            {
                for (Index index = 2; index < 4; ++index)
                    line.registers[index].interval =
                        read(line.registers[index].number, instruction * 2);
                UInt base = line.registers[1].number;
                Index results[4];
                for (UInt lane = 0; lane < 4; ++lane)
                    results[lane] = write(base + lane, instruction * 2 + 1);
                line.registers[0].interval = results[2];
                line.registers[1].interval = results[0];
            }
        }
        else if (text.startsWith(toSlice("CS2R ")))
        {
            if (line.registers.getCount() != 1 || line.registers[0].number % 2 != 0 ||
                !text.endsWith(toSlice(", SRZ;")))
                valid = false;
            if (valid)
            {
                line.registers[0].interval = write(line.registers[0].number, instruction * 2 + 1);
                write(line.registers[0].number + 1, instruction * 2 + 1);
            }
        }
        else if (text.startsWith(toSlice("FSETP.")) || text.startsWith(toSlice("ISETP.")))
        {
            if ((!text.startsWith(toSlice("FSETP.EQ.FTZ.AND P0, PT, ")) &&
                 !text.startsWith(toSlice("FSETP.NEU.FTZ.AND P0, PT, ")) &&
                 !text.startsWith(toSlice("FSETP.LT.FTZ.AND P0, PT, ")) &&
                 !text.startsWith(toSlice("FSETP.GT.FTZ.AND P0, PT, ")) &&
                 !text.startsWith(toSlice("FSETP.GE.FTZ.AND P0, PT, ")) &&
                 !text.startsWith(toSlice("ISETP.NE.U32.AND P0, PT, "))) ||
                !text.endsWith(toSlice(", PT;")))
                valid = false;
            for (auto& token : line.registers)
                token.interval = read(token.number, instruction * 2);
        }
        else if (line.registers.getCount())
        {
            for (Index index = 1; index < line.registers.getCount(); ++index)
                line.registers[index].interval =
                    read(line.registers[index].number, instruction * 2);
            line.registers[0].interval = write(line.registers[0].number, instruction * 2 + 1);
            if (line.registers.getCount() > 1)
                intervals[line.registers[0].interval].preferredSource = line.registers[1].interval;
        }
        else
            valid = false;
        lines.add(line);
        ++instruction;
    }
    auto overlap = [](const NX2LiveInterval& a, const NX2LiveInterval& b)
    { return a.start <= b.end && b.start <= a.end; };
    for (Index index = 0; valid && index < intervals.getCount(); ++index)
    {
        auto& interval = intervals[index];
        List<UInt> candidates;
        if (interval.physicalRegister < kNX2AllocatableRegisterCount)
            candidates.add(interval.physicalRegister);
        else
        {
            UInt preferred = interval.preferredSource >= 0
                                 ? intervals[interval.preferredSource].physicalRegister
                                 : 255;
            if (preferred < kNX2AllocatableRegisterCount)
                candidates.add(preferred);
            for (UInt number = 0; number < kNX2AllocatableRegisterCount; ++number)
            {
                if (number != preferred)
                    candidates.add(number);
            }
        }
        bool assigned = false;
        for (UInt candidate : candidates)
        {
            bool available = true;
            for (Index other = 0; other < intervals.getCount(); ++other)
            {
                if (other != index && intervals[other].physicalRegister == candidate &&
                    overlap(interval, intervals[other]))
                    available = false;
            }
            if (available)
            {
                interval.physicalRegister = candidate;
                assigned = true;
                break;
            }
        }
        valid = assigned;
    }
    if (!valid)
    {
        sink->diagnose(
            Diagnostics::Unimplemented{
                .feature = "NX2 native register allocation requires defined inputs and at most "
                           "125 registers",
                .location = SourceLoc()});
        return SLANG_FAIL;
    }
    scheduleNX2Lines(lines, intervals, outputCount, output);
    return SLANG_OK;
}

struct NX2Operand
{
    enum class Kind
    {
        Register,
        Literal,
        IntegerLiteral,
        ConstantBuffer
    };
    Kind kind = Kind::Register;
    UInt index = 0;
    float literal = 0;
    bool absolute = false;
};

struct NX2ActiveLoop
{
    LoopRegion* region;
    UInt depth;
    UInt label;
};

struct NX2Emitter
{
    DiagnosticSink* sink;
    StringBuilder* assembly;
    NX2Interface nativeInterface;
    bool sceneTextureABI;
    bool failed = false;
    UInt sampledMask = 0;
    UInt nextRegister = 11;
    Dictionary<IRInst*, List<NX2Operand>> values;
    Dictionary<uint32_t, NX2Operand> literalRegisters;
    Dictionary<IRInst*, List<UInt>> outputLocations;
    Dictionary<IRInst*, List<NX2Operand>> localVariables;
    HashSet<IRBlock*> emittedBlocks;
    UInt nextLabel = 0;
    IRFunc* currentFunction = nullptr;
    List<NX2ActiveLoop> activeLoops;
    bool inConditionalEntryBlock = false;

    void markOutput(IRInst* inst, UInt lane, UInt location)
    {
        if (inst->getOp() == kIROp_MakeVector)
        {
            for (UInt index = 0; index < inst->getOperandCount(); ++index)
            {
                UInt count = width(inst->getOperand(index)->getDataType());
                if (lane < count)
                {
                    markOutput(inst->getOperand(index), lane, location);
                    return;
                }
                lane -= count;
            }
        }
        else if (auto swizzle = as<IRSwizzle>(inst))
            markOutput(
                swizzle->getBase(),
                UInt(getIntVal(swizzle->getElementIndex(lane))),
                location);
        else if (auto invocation = as<IRCall>(inst))
        {
            // A call used only by the return can write the fixed output bank safely.
            for (auto use = inst->firstUse; use; use = use->nextUse)
            {
                auto user = use->getUser();
                if (user->getOp() != kIROp_MakeVector && user->getOp() != kIROp_Return)
                    return;
            }
            auto locations = outputLocations.tryGetValue(invocation);
            if (!locations)
            {
                List<UInt> initial;
                for (UInt index = 0; index < width(inst->getDataType()); ++index)
                    initial.add(255);
                outputLocations.add(invocation, initial);
                locations = outputLocations.tryGetValue(invocation);
            }
            if (lane < UInt(locations->getCount()))
                (*locations)[lane] = location;
        }
    }

    void reject(IRInst* inst)
    {
        if (failed)
            return;
        failed = true;
        sink->diagnose(
            Diagnostics::Unimplemented{
                .feature = "NX2 SASS emitter currently requires supported float IR and an explicit "
                           "native resource contract",
                .location = inst->sourceLoc});
    }

    UInt width(IRType* type)
    {
        if (type->getOp() == kIROp_FloatType)
            return 1;
        if (auto vector = as<IRVectorType>(type))
        {
            if (vector->getElementType()->getOp() == kIROp_FloatType)
            {
                auto count = getIntVal(vector->getElementCount());
                if (count >= 1 && count <= 4)
                    return UInt(count);
            }
        }
        return 0;
    }

    String operand(NX2Operand value)
    {
        StringBuilder text;
        if (value.absolute)
            text << "|";
        switch (value.kind)
        {
        case NX2Operand::Kind::Register:
            text << "R" << value.index;
            break;
        case NX2Operand::Kind::Literal:
            text << StringUtil::makeStringWithFormat("%.20e", double(value.literal));
            break;
        case NX2Operand::Kind::IntegerLiteral:
            text << StringUtil::makeStringWithFormat("0x%08x", value.index);
            break;
        case NX2Operand::Kind::ConstantBuffer:
            text << "c[0x3][" << StringUtil::makeStringWithFormat("0x%x", value.index) << "]";
            break;
        }
        if (value.absolute)
            text << "|";
        return text;
    }

    void move(UInt destination, NX2Operand value)
    {
        if (value.kind == NX2Operand::Kind::Literal ||
            value.kind == NX2Operand::Kind::IntegerLiteral)
        {
            uint32_t bits = 0;
            if (value.kind == NX2Operand::Kind::IntegerLiteral)
                bits = value.index;
            else
                ::memcpy(&bits, &value.literal, sizeof(bits));
            if (value.absolute)
                bits &= 0x7fffffff;
            *assembly << "MOV R" << destination << ", "
                      << StringUtil::makeStringWithFormat("0x%08x", bits) << ";\n";
        }
        else if (value.absolute)
            failed = true;
        else if (value.kind == NX2Operand::Kind::Register && value.index == destination)
            return;
        else
            *assembly << "MOV R" << destination << ", " << operand(value) << ";\n";
    }

    NX2Operand allocate(IRInst*) { return {NX2Operand::Kind::Register, nextRegister++}; }

    NX2Operand reg(IRInst* inst, NX2Operand value)
    {
        if (value.kind == NX2Operand::Kind::Register)
            return value;
        uint32_t bits = 0;
        if (value.kind == NX2Operand::Kind::Literal)
        {
            ::memcpy(&bits, &value.literal, sizeof(bits));
            if (value.absolute)
                bits &= 0x7fffffff;
            if (auto found = literalRegisters.tryGetValue(bits))
                return *found;
        }
        auto result = allocate(inst);
        move(result.index, value);
        if (value.kind == NX2Operand::Kind::Literal)
            literalRegisters.add(bits, result);
        return result;
    }

    NX2Operand binary(IRInst* inst, const char* opcode, NX2Operand a, NX2Operand b)
    {
        a = reg(inst, a);
        auto result = allocate(inst);
        *assembly << opcode << " " << operand(result) << ", " << operand(a) << ", " << operand(b);
        *assembly << ";\n";
        return result;
    }

    bool binding(IRInst* inst, LayoutResourceKind kind, UInt index)
    {
        auto layout = findVarLayout(inst);
        auto offset = layout ? layout->findOffsetAttr(kind) : nullptr;
        return offset && offset->getOffset() == index && offset->getSpace() == 0;
    }

    List<NX2Operand> load(IRInst* inst)
    {
        List<NX2Operand> result;
        auto pointer = inst->getOperand(0);
        if (auto local = localVariables.tryGetValue(pointer))
        {
            for (auto source : *local)
            {
                auto destination = allocate(inst);
                move(destination.index, source);
                result.add(destination);
            }
            return result;
        }
        if (pointer->getOp() != kIROp_GetElementPtr)
        {
            reject(inst);
            return result;
        }
        auto field = pointer->getOperand(0);
        auto index = as<IRIntLit>(pointer->getOperand(1));
        if (field->getOp() != kIROp_FieldAddress || !index || index->getValue() < 0)
        {
            reject(inst);
            return result;
        }
        auto global = field->getOperand(0);
        auto layout = findVarLayout(global);
        auto group = layout ? as<IRParameterGroupTypeLayout>(layout->getTypeLayout()) : nullptr;
        auto structure =
            group ? as<IRStructTypeLayout>(group->getElementVarLayout()->getTypeLayout()) : nullptr;
        auto array = as<IRArrayType>(cast<IRPtrTypeBase>(field->getDataType())->getValueType());
        if (!binding(global, LayoutResourceKind::ConstantBuffer, 3) || !structure ||
            structure->getFieldCount() != 1 ||
            structure->getFieldLayoutAttrs()[0]->getOperand(0) != field->getOperand(1) || !array ||
            width(array->getElementType()) != 4 ||
            index->getValue() >= getIntVal(array->getElementCount()) ||
            width(inst->getDataType()) != 4)
        {
            reject(inst);
            return result;
        }
        auto offset = structure->getFieldLayout(0)->findOffsetAttr(LayoutResourceKind::Uniform);
        if (!offset || offset->getOffset() != 0 || index->getValue() > 4094)
        {
            reject(inst);
            return result;
        }
        for (UInt lane = 0; lane < 4; ++lane)
            result.add({NX2Operand::Kind::ConstantBuffer, UInt(index->getValue()) * 16 + lane * 4});
        return result;
    }

    List<NX2Operand> call(IRCall* inst)
    {
        List<NX2Operand> result;
        auto function = as<IRFunc>(inst->getOperand(0));
        auto block = function ? function->getFirstBlock() : nullptr;
        auto terminator = block ? block->getTerminator() : nullptr;
        if (!block || block->getNextBlock() || !terminator ||
            terminator->getOp() != kIROp_GenericAsm)
        {
            reject(inst);
            return result;
        }
        for (auto instruction : block->getOrdinaryInsts())
        {
            if (instruction != terminator && instruction->getOp() != kIROp_RequireComputeDerivative)
                reject(inst);
        }
        auto text = as<IRStringLit>(terminator->getOperand(0));
        if (!text)
        {
            reject(inst);
            return result;
        }
        auto name = text->getStringSlice();
        if ((name == toSlice("nx2_asfloat") || name == toSlice("nx2_asuint")) &&
            inst->getArgCount() == 1)
        {
            auto operands = value(inst->getArg(0));
            if (operands.getCount() < 1 || operands.getCount() > 4)
            {
                reject(inst);
                return result;
            }
            for (auto operandValue : operands)
            {
                if (operandValue.absolute)
                {
                    reject(inst);
                    return result;
                }
                if (name == toSlice("nx2_asfloat") &&
                    operandValue.kind == NX2Operand::Kind::IntegerLiteral)
                {
                    float converted;
                    ::memcpy(&converted, &operandValue.index, sizeof(converted));
                    operandValue = {NX2Operand::Kind::Literal, 0, converted};
                }
                result.add(operandValue);
            }
            return result;
        }
        if (name == toSlice("nx2_sample"))
        {
            auto texture = inst->getArgCount() == 3
                               ? as<IRTextureTypeBase>(inst->getArg(0)->getDataType())
                               : nullptr;
            UInt slot = sceneTextureABI && inst->getArgCount() == 3 &&
                                binding(inst->getArg(0), LayoutResourceKind::ShaderResource, 1) &&
                                binding(inst->getArg(1), LayoutResourceKind::SamplerState, 1)
                            ? 1
                            : 0;
            if ((sampledMask & (1u << slot)) || inst->getArgCount() != 3 || !texture ||
                texture->getShape() != SLANG_TEXTURE_2D || texture->isMultisample() ||
                texture->isShadow() || texture->isCombined() ||
                texture->getAccess() != SLANG_RESOURCE_ACCESS_READ ||
                width(texture->getElementType()) != 4 ||
                !binding(inst->getArg(0), LayoutResourceKind::ShaderResource, slot) ||
                !binding(inst->getArg(1), LayoutResourceKind::SamplerState, slot) ||
                (sceneTextureABI && nativeInterface != NX2Interface::PerspectiveTexture) ||
                width(inst->getDataType()) != 4)
            {
                reject(inst);
                return result;
            }
            auto uv = value(inst->getArg(2));
            if (uv.getCount() != 2 || uv[0].kind != NX2Operand::Kind::Register ||
                uv[1].kind != NX2Operand::Kind::Register ||
                (nativeInterface == NX2Interface::PerspectiveTexture && !inConditionalEntryBlock &&
                 (uv[0].index != 8 || uv[1].index != 9)))
            {
                reject(inst);
                return result;
            }
            if (nativeInterface == NX2Interface::ScreenTexture || inConditionalEntryBlock)
            {
                move(8, uv[0]);
                move(9, uv[1]);
            }
            sampledMask |= 1u << slot;
            *assembly << "TEX.SCR.NODEP R2, R0, R8, R9, 0x2, " << (slot == 0 ? "0x8" : "0xa")
                      << ", 2D;\n";
            for (UInt lane = 0; lane < 4; ++lane)
            {
                NX2Operand sample{NX2Operand::Kind::Register, lane};
                if (sceneTextureABI || inConditionalEntryBlock)
                {
                    auto saved = allocate(inst);
                    move(saved.index, sample);
                    sample = saved;
                }
                result.add(sample);
            }
            return result;
        }
        if (inst->getArgCount() == 0)
        {
            reject(inst);
            return result;
        }
        auto a = value(inst->getArg(0));
        if (name == toSlice("nx2_any_scalar") && inst->getArgCount() == 1)
        {
            if (inst->getArg(0)->getDataType()->getOp() != kIROp_BoolType || a.getCount() != 1)
                reject(inst);
            else
                result.add(a[0]);
            return result;
        }
        if ((name == toSlice("nx2_isinf") || name == toSlice("nx2_isnan") ||
             name == toSlice("nx2_isfinite")) &&
            inst->getArgCount() == 1)
        {
            UInt count = width(inst->getArg(0)->getDataType());
            if (!count || a.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            NX2Operand limit;
            if (name != toSlice("nx2_isnan"))
            {
                uint32_t infinityBits = 0x7f800000;
                float infinity;
                ::memcpy(&infinity, &infinityBits, sizeof(infinity));
                limit = reg(inst, {NX2Operand::Kind::Literal, 0, infinity});
            }
            for (auto source : a)
            {
                source = reg(inst, source);
                if (name != toSlice("nx2_isnan"))
                    source.absolute = true;
                auto destination = allocate(inst);
                auto opcode = name == toSlice("nx2_isinf")      ? "FSETP.EQ.FTZ.AND"
                              : name == toSlice("nx2_isfinite") ? "FSETP.LT.FTZ.AND"
                                                                : "FSETP.NEU.FTZ.AND";
                *assembly << opcode << " P0, PT, " << operand(source) << ", "
                          << operand(name == toSlice("nx2_isnan") ? source : limit) << ", PT;\nSEL "
                          << operand(destination) << ", RZ, 0x1, !P0;\n";
                result.add(destination);
            }
            return result;
        }
        if ((name == toSlice("nx2_all") || name == toSlice("nx2_any")) && inst->getArgCount() == 1)
        {
            auto type = as<IRVectorType>(inst->getArg(0)->getDataType());
            if (!type || type->getElementType()->getOp() != kIROp_BoolType ||
                inst->getDataType()->getOp() != kIROp_BoolType || a.getCount() < 1 ||
                a.getCount() > 4)
            {
                reject(inst);
                return result;
            }
            auto accumulated = reg(inst, a[0]);
            for (Index lane = 1; lane < a.getCount(); ++lane)
            {
                auto next = reg(inst, a[lane]);
                auto destination = allocate(inst);
                *assembly << "LOP3.LUT " << operand(destination) << ", " << operand(accumulated)
                          << ", " << operand(next) << ", RZ, "
                          << (name == toSlice("nx2_all") ? "0xc0" : "0xfc") << ", !PT;\n";
                accumulated = destination;
            }
            result.add(accumulated);
            return result;
        }
        if (name == toSlice("nx2_pow") && inst->getArgCount() == 2)
        {
            auto b = value(inst->getArg(1));
            UInt count = width(inst->getDataType());
            if (!count || a.getCount() != Index(count) || b.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            for (UInt lane = 0; lane < count; ++lane)
            {
                auto base = reg(inst, a[lane]);
                auto logarithm = allocate(inst);
                *assembly << "MUFU.LG2 " << operand(logarithm) << ", " << operand(base) << ";\n";
                auto exponent = binary(inst, "FMUL.FTZ", logarithm, b[lane]);
                auto power = allocate(inst);
                *assembly << "MUFU.EX2 " << operand(power) << ", " << operand(exponent) << ";\n";
                result.add(power);
            }
            return result;
        }
        if ((name == toSlice("nx2_log10") || name == toSlice("nx2_log") ||
             name == toSlice("nx2_exp")) &&
            inst->getArgCount() == 1)
        {
            UInt count = width(inst->getDataType());
            if (!count || a.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            for (auto source : a)
            {
                source = reg(inst, source);
                if (name == toSlice("nx2_exp"))
                {
                    auto scaled = binary(
                        inst,
                        "FMUL.FTZ",
                        source,
                        {NX2Operand::Kind::Literal, 0, 1.4426950408889634074f});
                    auto exponent = allocate(inst);
                    *assembly << "MUFU.EX2 " << operand(exponent) << ", " << operand(scaled)
                              << ";\n";
                    result.add(exponent);
                    continue;
                }
                auto logarithm = allocate(inst);
                *assembly << "MUFU.LG2 " << operand(logarithm) << ", " << operand(source) << ";\n";
                result.add(binary(
                    inst,
                    "FMUL.FTZ",
                    logarithm,
                    {NX2Operand::Kind::Literal,
                     0,
                     name == toSlice("nx2_log10") ? 0.30102999566398119521f
                                                  : 0.69314718055994530942f}));
            }
            return result;
        }
        if (name == toSlice("nx2_lerp") && inst->getArgCount() == 3)
        {
            auto b = value(inst->getArg(1));
            auto factor = value(inst->getArg(2));
            UInt count = width(inst->getDataType());
            if (!count || a.getCount() != Index(count) || b.getCount() != Index(count) ||
                factor.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            for (UInt lane = 0; lane < count; ++lane)
            {
                auto start = reg(inst, a[lane]);
                auto end = reg(inst, b[lane]);
                auto difference = allocate(inst);
                *assembly << "FADD.FTZ " << operand(difference) << ", " << operand(end) << ", -"
                          << operand(start) << ";\n";
                auto scaled = binary(inst, "FMUL.FTZ", difference, factor[lane]);
                result.add(binary(inst, "FADD.FTZ", start, scaled));
            }
            return result;
        }
        if (name == toSlice("nx2_saturate") && inst->getArgCount() == 1)
        {
            UInt count = width(inst->getDataType());
            if (!count || a.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            for (auto source : a)
            {
                auto destination = allocate(inst);
                *assembly << "FADD.FTZ.SAT " << operand(destination) << ", RZ, " << operand(source)
                          << ";\n";
                result.add(destination);
            }
            return result;
        }
        if ((name == toSlice("nx2_min") || name == toSlice("nx2_max")) && inst->getArgCount() == 2)
        {
            auto b = value(inst->getArg(1));
            UInt count = width(inst->getDataType());
            if (!count || a.getCount() != Index(count) || b.getCount() != Index(count))
            {
                reject(inst);
                return result;
            }
            for (UInt lane = 0; lane < count; ++lane)
            {
                auto source = reg(inst, a[lane]);
                auto destination = allocate(inst);
                *assembly << "FMNMX.FTZ " << operand(destination) << ", " << operand(source) << ", "
                          << operand(b[lane])
                          << (name == toSlice("nx2_min") ? ", PT;\n" : ", !PT;\n");
                result.add(destination);
            }
            return result;
        }
        if (name == toSlice("nx2_dot") && inst->getArgCount() == 2)
        {
            auto b = value(inst->getArg(1));
            if (a.getCount() != 3 || b.getCount() != 3 || width(inst->getDataType()) != 1)
            {
                reject(inst);
                return result;
            }
            auto sum = binary(inst, "FMUL.FTZ", a[1], b[1]);
            for (UInt lane : {UInt(0), UInt(2)})
            {
                auto source = reg(inst, a[lane]);
                *assembly << "FFMA.FTZ " << operand(sum) << ", " << operand(source) << ", "
                          << operand(b[lane]) << ", " << operand(sum) << ";\n";
            }
            result.add(sum);
            return result;
        }
        if (inst->getArgCount() != 1 || a.getCount() != Index(width(inst->getDataType())))
        {
            reject(inst);
            return result;
        }
        bool canWriteOutputBank = true;
        for (auto source : a)
        {
            if (source.kind == NX2Operand::Kind::Register && source.index < 4)
                canWriteOutputBank = false;
        }
        UInt lane = 0;
        for (auto source : a)
        {
            if (name == toSlice("nx2_abs"))
            {
                source.absolute = true;
                result.add(source);
            }
            else if (
                name == toSlice("nx2_log2") || name == toSlice("nx2_exp2") ||
                name == toSlice("nx2_sqrt") || name == toSlice("nx2_rsqrt") ||
                name == toSlice("nx2_rcp"))
            {
                source = reg(inst, source);
                auto destination = allocate(inst);
                if (auto locations = outputLocations.tryGetValue(inst))
                {
                    if (canWriteOutputBank && (*locations)[lane] < 4)
                        destination.index = (*locations)[lane];
                }
                auto opcode = name == toSlice("nx2_log2")    ? "MUFU.LG2 "
                              : name == toSlice("nx2_exp2")  ? "MUFU.EX2 "
                              : name == toSlice("nx2_sqrt")  ? "MUFU.SQRT "
                              : name == toSlice("nx2_rsqrt") ? "MUFU.RSQ "
                                                             : "MUFU.RCP ";
                *assembly << opcode << operand(destination) << ", " << operand(source) << ";\n";
                result.add(destination);
            }
            else
                reject(inst);
            ++lane;
        }
        return result;
    }

    List<NX2Operand> value(IRInst* inst)
    {
        if (auto found = values.tryGetValue(inst))
            return *found;
        List<NX2Operand> result;
        if (auto literal = as<IRFloatLit>(inst))
            result.add({NX2Operand::Kind::Literal, 0, float(literal->getValue())});
        else if (auto literal = as<IRBoolLit>(inst))
            result.add({NX2Operand::Kind::IntegerLiteral, literal->getValue() ? 1u : 0u});
        else if (auto literal = as<IRIntLit>(inst))
        {
            auto type = literal->getDataType()->getOp();
            if (type != kIROp_IntType && type != kIROp_UIntType)
                reject(inst);
            else
                result.add({NX2Operand::Kind::IntegerLiteral, uint32_t(literal->getValue())});
        }
        else if (auto swizzle = as<IRSwizzle>(inst))
        {
            auto base = value(swizzle->getBase());
            for (UInt lane = 0; lane < swizzle->getElementCount(); ++lane)
            {
                auto index = as<IRIntLit>(swizzle->getElementIndex(lane));
                if (index && index->getValue() >= 0 && index->getValue() < base.getCount())
                    result.add(base[Index(index->getValue())]);
                else
                    reject(inst);
            }
        }
        else if (
            inst->getOp() == kIROp_GetElement &&
            as<IRVectorType>(inst->getOperand(0)->getDataType()))
        {
            auto base = value(inst->getOperand(0));
            auto index = value(inst->getOperand(1));
            auto indexType = inst->getOperand(1)->getDataType()->getOp();
            if (!width(inst->getOperand(0)->getDataType()) || index.getCount() != 1 ||
                (indexType != kIROp_IntType && indexType != kIROp_UIntType))
                reject(inst);
            if (!failed)
            {
                if (auto literal = as<IRIntLit>(inst->getOperand(1)))
                {
                    if (literal->getValue() < 0 || literal->getValue() >= base.getCount())
                        reject(inst);
                    else
                        result.add(base[Index(literal->getValue())]);
                }
                else
                {
                    auto indexRegister = reg(inst, index[0]);
                    auto selected = reg(inst, base[0]);
                    for (Index lane = 1; lane < base.getCount(); ++lane)
                    {
                        auto candidate = reg(inst, base[lane]);
                        auto destination = allocate(inst);
                        *assembly << "ISETP.NE.U32.AND P0, PT, " << operand(indexRegister) << ", 0x"
                                  << UInt(lane) << ", PT;\nSEL " << operand(destination) << ", "
                                  << operand(selected) << ", " << operand(candidate) << ", P0;\n";
                        selected = destination;
                    }
                    result.add(selected);
                }
            }
        }
        else if (inst->getOp() == kIROp_MakeVector)
        {
            for (UInt index = 0; index < inst->getOperandCount(); ++index)
                result.addRange(value(inst->getOperand(index)));
        }
        else if (inst->getOp() == kIROp_MakeVectorFromScalar)
        {
            auto vector = as<IRVectorType>(inst->getDataType());
            auto scalar = value(inst->getOperand(0));
            UInt count = width(inst->getDataType());
            if (!vector || !count || scalar.getCount() != 1 ||
                vector->getElementType() != inst->getOperand(0)->getDataType())
                reject(inst);
            else
                for (UInt lane = 0; lane < count; ++lane)
                    result.add(scalar[0]);
        }
        else if (inst->getOp() == kIROp_Load)
            result = load(inst);
        else if (auto invocation = as<IRCall>(inst))
            result = call(invocation);
        else if (inst->getOp() == kIROp_Neg)
        {
            auto source = value(inst->getOperand(0));
            auto count = width(inst->getDataType());
            if (!count || source.getCount() != Index(count))
                reject(inst);
            if (!failed)
            {
                auto sign = reg(inst, {NX2Operand::Kind::IntegerLiteral, 0x80000000u});
                for (auto lane : source)
                {
                    bool absolute = lane.absolute;
                    lane.absolute = false;
                    auto input = reg(inst, lane);
                    auto destination = allocate(inst);
                    *assembly << "LOP3.LUT " << operand(destination) << ", " << operand(input)
                              << ", " << operand(sign) << ", RZ, " << (absolute ? "0xfc" : "0x3c")
                              << ", !PT;\n";
                    result.add(destination);
                }
            }
        }
        else if (inst->getOp() == kIROp_CastFloatToInt)
        {
            auto source = value(inst->getOperand(0));
            if (inst->getDataType()->getOp() != kIROp_IntType ||
                inst->getOperand(0)->getDataType()->getOp() != kIROp_FloatType ||
                source.getCount() != 1)
                reject(inst);
            if (!failed)
            {
                auto input = reg(inst, source[0]);
                auto destination = allocate(inst);
                *assembly << "F2I.FTZ.TRUNC.NTZ " << operand(destination) << ", " << operand(input)
                          << ";\n";
                result.add(destination);
            }
        }
        else if (
            (inst->getOp() == kIROp_Eql || inst->getOp() == kIROp_Neq) &&
            (inst->getOperand(0)->getDataType()->getOp() == kIROp_IntType ||
             inst->getOperand(0)->getDataType()->getOp() == kIROp_UIntType) &&
            inst->getOperand(0)->getDataType() == inst->getOperand(1)->getDataType())
        {
            auto left = value(inst->getOperand(0));
            auto right = value(inst->getOperand(1));
            if (left.getCount() != 1 || right.getCount() != 1)
                reject(inst);
            if (!failed)
            {
                auto a = reg(inst, left[0]);
                auto b = reg(inst, right[0]);
                auto destination = allocate(inst);
                *assembly << "ISETP.NE.U32.AND P0, PT, " << operand(a) << ", " << operand(b)
                          << ", PT;\nSEL " << operand(destination) << ", RZ, 0x1, "
                          << (inst->getOp() == kIROp_Eql ? "P0;\n" : "!P0;\n");
                result.add(destination);
            }
        }
        else if (
            inst->getOp() == kIROp_Less &&
            inst->getOperand(0)->getDataType()->getOp() == kIROp_IntType &&
            inst->getOperand(1)->getDataType()->getOp() == kIROp_IntType)
        {
            auto left = value(inst->getOperand(0));
            auto right = value(inst->getOperand(1));
            if (left.getCount() != 1 || right.getCount() != 1)
                reject(inst);
            if (!failed)
            {
                auto a = reg(inst, left[0]);
                auto b = reg(inst, right[0]);
                auto destination = allocate(inst);
                *assembly << "ISETP.LT.AND P0, PT, " << operand(a) << ", " << operand(b)
                          << ", PT;\nSEL " << operand(destination) << ", RZ, 0x1, !P0;\n";
                result.add(destination);
            }
        }
        else if (
            inst->getOp() == kIROp_Eql || inst->getOp() == kIROp_Neq ||
            inst->getOp() == kIROp_Greater || inst->getOp() == kIROp_Geq ||
            inst->getOp() == kIROp_Less)
        {
            auto left = value(inst->getOperand(0));
            auto right = value(inst->getOperand(1));
            auto leftWidth = width(inst->getOperand(0)->getDataType());
            auto rightWidth = width(inst->getOperand(1)->getDataType());
            auto count = leftWidth > rightWidth ? leftWidth : rightWidth;
            if (!leftWidth || !rightWidth ||
                (left.getCount() != 1 && left.getCount() != Index(count)) ||
                (right.getCount() != 1 && right.getCount() != Index(count)))
                reject(inst);
            if (!failed)
            {
                for (UInt lane = 0; lane < count; ++lane)
                {
                    auto a = reg(inst, left[left.getCount() == 1 ? 0 : lane]);
                    auto b = right[right.getCount() == 1 ? 0 : lane];
                    bool zero = b.kind == NX2Operand::Kind::Literal && b.literal == 0.0f;
                    if (!zero)
                        b = reg(inst, b);
                    auto destination = allocate(inst);
                    *assembly << (inst->getOp() == kIROp_Greater ? "FSETP.GT.FTZ.AND P0, PT, "
                                  : inst->getOp() == kIROp_Geq   ? "FSETP.GE.FTZ.AND P0, PT, "
                                  : inst->getOp() == kIROp_Less  ? "FSETP.LT.FTZ.AND P0, PT, "
                                                                 : "FSETP.EQ.FTZ.AND P0, PT, ")
                              << operand(a) << ", " << (zero ? String("RZ") : operand(b))
                              << ", PT;\nSEL " << operand(destination) << ", RZ, 0x1, "
                              << (inst->getOp() == kIROp_Neq ? "P0;\n" : "!P0;\n");
                    result.add(destination);
                }
            }
        }
        else if (auto select = as<IRSelect>(inst))
        {
            auto condition = value(select->getCondition());
            auto ifTrue = value(select->getTrueResult());
            auto ifFalse = value(select->getFalseResult());
            auto count = width(inst->getDataType());
            if (condition.getCount() != 1 || !count || ifTrue.getCount() != Index(count) ||
                ifFalse.getCount() != Index(count))
                reject(inst);
            if (!failed)
            {
                auto predicate = reg(inst, condition[0]);
                *assembly << "ISETP.NE.U32.AND P0, PT, " << operand(predicate) << ", RZ, PT;\n";
                for (UInt lane = 0; lane < count; ++lane)
                {
                    auto a = reg(inst, ifTrue[lane]);
                    auto b = reg(inst, ifFalse[lane]);
                    auto destination = allocate(inst);
                    *assembly << "SEL " << operand(destination) << ", " << operand(a) << ", "
                              << operand(b) << ", P0;\n";
                    result.add(destination);
                }
            }
        }
        else if (inst->getOp() == kIROp_BitAnd || inst->getOp() == kIROp_BitOr)
        {
            auto left = value(inst->getOperand(0));
            auto right = value(inst->getOperand(1));
            auto type = inst->getDataType();
            auto vector = as<IRVectorType>(type);
            auto element = vector ? vector->getElementType() : type;
            Index count = vector ? Index(getIntVal(vector->getElementCount())) : 1;
            if ((element->getOp() != kIROp_UIntType && element->getOp() != kIROp_IntType) ||
                count < 1 || count > 4 || (left.getCount() != 1 && left.getCount() != count) ||
                (right.getCount() != 1 && right.getCount() != count))
                reject(inst);
            if (!failed)
            {
                for (Index lane = 0; lane < count; ++lane)
                {
                    auto a = reg(inst, left[left.getCount() == 1 ? 0 : lane]);
                    auto b = reg(inst, right[right.getCount() == 1 ? 0 : lane]);
                    auto destination = allocate(inst);
                    *assembly << "LOP3.LUT " << operand(destination) << ", " << operand(a) << ", "
                              << operand(b) << ", RZ, "
                              << (inst->getOp() == kIROp_BitAnd ? "0xc0" : "0xfc") << ", !PT;\n";
                    result.add(destination);
                }
            }
        }
        else if (
            inst->getOp() == kIROp_Add && (inst->getDataType()->getOp() == kIROp_IntType ||
                                           inst->getDataType()->getOp() == kIROp_UIntType))
        {
            auto left = value(inst->getOperand(0));
            auto right = value(inst->getOperand(1));
            if (left.getCount() != 1 || right.getCount() != 1 ||
                inst->getOperand(0)->getDataType() != inst->getDataType() ||
                inst->getOperand(1)->getDataType() != inst->getDataType())
                reject(inst);
            if (!failed)
            {
                auto source = reg(inst, left[0]);
                auto destination = allocate(inst);
                *assembly << "IADD3 " << operand(destination) << ", " << operand(source) << ", "
                          << operand(right[0]) << ", RZ;\n";
                result.add(destination);
            }
        }
        else if (
            inst->getOp() == kIROp_Mul || inst->getOp() == kIROp_Add ||
            inst->getOp() == kIROp_Sub || inst->getOp() == kIROp_Div)
        {
            auto product = inst->getOperand(0);
            if (inst->getOp() == kIROp_Add && product->getOp() == kIROp_Mul &&
                !inst->findDecoration<IRPreciseDecoration>() &&
                !product->findDecoration<IRPreciseDecoration>())
            {
                auto a = value(product->getOperand(0));
                auto b = value(product->getOperand(1));
                auto c = value(inst->getOperand(1));
                UInt count = width(inst->getDataType());
                if (!count || (a.getCount() != 1 && a.getCount() != Index(count)) ||
                    (b.getCount() != 1 && b.getCount() != Index(count)) ||
                    (c.getCount() != 1 && c.getCount() != Index(count)))
                    reject(inst);
                if (!failed)
                {
                    for (UInt lane = 0; lane < count; ++lane)
                    {
                        auto left = reg(inst, a[a.getCount() == 1 ? 0 : lane]);
                        auto right = reg(inst, b[b.getCount() == 1 ? 0 : lane]);
                        auto destination = allocate(inst);
                        *assembly << "FFMA.FTZ " << operand(destination) << ", " << operand(left)
                                  << ", " << operand(right) << ", "
                                  << operand(c[c.getCount() == 1 ? 0 : lane]) << ";\n";
                        result.add(destination);
                    }
                }
                values.add(inst, result);
                return result;
            }
            auto a = value(inst->getOperand(0));
            auto b = value(inst->getOperand(1));
            UInt count = width(inst->getDataType());
            if ((a.getCount() != 1 && a.getCount() != Index(count)) ||
                (b.getCount() != 1 && b.getCount() != Index(count)) || !count)
                reject(inst);
            if (!failed)
            {
                for (UInt lane = 0; lane < count; ++lane)
                {
                    auto left = a[a.getCount() == 1 ? 0 : lane];
                    auto right = b[b.getCount() == 1 ? 0 : lane];
                    if (inst->getOp() == kIROp_Div)
                    {
                        right = reg(inst, right);
                        auto reciprocal = allocate(inst);
                        *assembly << "MUFU.RCP " << operand(reciprocal) << ", " << operand(right)
                                  << ";\n";
                        right = reciprocal;
                    }
                    if (inst->getOp() == kIROp_Sub)
                    {
                        left = reg(inst, left);
                        auto destination = allocate(inst);
                        *assembly << "FADD.FTZ " << operand(destination) << ", " << operand(left)
                                  << ", ";
                        if (right.kind == NX2Operand::Kind::Literal)
                        {
                            uint32_t bits;
                            ::memcpy(&bits, &right.literal, sizeof(bits));
                            if (right.absolute)
                                bits &= 0x7fffffff;
                            bits ^= 0x80000000;
                            ::memcpy(&right.literal, &bits, sizeof(bits));
                            right.absolute = false;
                            *assembly << operand(right);
                        }
                        else
                            *assembly << "-" << operand(right);
                        *assembly << ";\n";
                        result.add(destination);
                    }
                    else
                        result.add(binary(
                            inst,
                            inst->getOp() == kIROp_Add ? "FADD.FTZ" : "FMUL.FTZ",
                            left,
                            right));
                }
            }
        }
        else
            reject(inst);
        values.add(inst, result);
        return result;
    }

    // Emit structured regions without moving work across branch arms.
    // For example, a guarded division stays inside its original arm.
    void emitConditionalRegion(Region* region, UInt depth, UInt outputCount)
    {
        if (!region || failed)
            return;
        switch (region->getFlavor())
        {
        case Region::Flavor::Simple:
            {
                auto simple = static_cast<SimpleRegion*>(region);
                auto block = simple->block;
                if (emittedBlocks.contains(block))
                {
                    reject(block);
                    return;
                }
                emittedBlocks.add(block);
                literalRegisters.clear();
                for (auto inst : block->getOrdinaryInsts())
                {
                    switch (inst->getOp())
                    {
                    case kIROp_Var:
                        {
                            auto pointerType = as<IRPtrTypeBase>(inst->getDataType());
                            UInt count = pointerType ? width(pointerType->getValueType()) : 0;
                            if (pointerType &&
                                (pointerType->getValueType()->getOp() == kIROp_IntType ||
                                 pointerType->getValueType()->getOp() == kIROp_UIntType ||
                                 pointerType->getValueType()->getOp() == kIROp_BoolType))
                                count = 1;
                            if (!count)
                            {
                                reject(inst);
                                break;
                            }
                            List<NX2Operand> registers;
                            for (UInt lane = 0; lane < count; ++lane)
                                registers.add(allocate(inst));
                            localVariables.add(inst, registers);
                        }
                        break;
                    case kIROp_Store:
                        {
                            auto store = as<IRStore>(inst);
                            auto local = localVariables.tryGetValue(store->getPtr());
                            auto source = value(store->getVal());
                            if (local && local->getCount() == source.getCount())
                            {
                                for (Index lane = 0; lane < source.getCount(); ++lane)
                                    move((*local)[lane].index, source[lane]);
                            }
                            else if (
                                store->getPtr()->getOp() == kIROp_GetElementPtr &&
                                source.getCount() == 1)
                            {
                                auto address = store->getPtr();
                                auto vectorLocal =
                                    localVariables.tryGetValue(address->getOperand(0));
                                auto pointer =
                                    as<IRPtrTypeBase>(address->getOperand(0)->getDataType());
                                auto vector =
                                    pointer ? as<IRVectorType>(pointer->getValueType()) : nullptr;
                                auto index = value(address->getOperand(1));
                                auto indexType = address->getOperand(1)->getDataType()->getOp();
                                if (!vectorLocal || !vector || index.getCount() != 1 ||
                                    (indexType != kIROp_IntType && indexType != kIROp_UIntType))
                                {
                                    reject(inst);
                                    break;
                                }
                                if (auto literal = as<IRIntLit>(address->getOperand(1)))
                                {
                                    if (literal->getValue() < 0 ||
                                        literal->getValue() >= vectorLocal->getCount())
                                        reject(inst);
                                    else
                                        move(
                                            (*vectorLocal)[Index(literal->getValue())].index,
                                            source[0]);
                                }
                                else
                                {
                                    auto indexRegister = reg(inst, index[0]);
                                    auto replacement = reg(inst, source[0]);
                                    for (Index lane = 0; lane < vectorLocal->getCount(); ++lane)
                                    {
                                        auto destination = allocate(inst);
                                        *assembly << "ISETP.NE.U32.AND P0, PT, "
                                                  << operand(indexRegister) << ", 0x" << UInt(lane)
                                                  << ", PT;\nSEL " << operand(destination) << ", "
                                                  << operand((*vectorLocal)[lane]) << ", "
                                                  << operand(replacement) << ", P0;\n";
                                        move((*vectorLocal)[lane].index, destination);
                                    }
                                }
                            }
                            else
                                reject(inst);
                        }
                        break;
                    case kIROp_Return:
                        {
                            if (depth || inst->getOperandCount() != 1)
                            {
                                reject(inst);
                                break;
                            }
                            auto output = value(inst->getOperand(0));
                            if (output.getCount() != Index(outputCount))
                            {
                                reject(inst);
                                break;
                            }
                            for (UInt lane = 0; lane < outputCount; ++lane)
                                move(lane, output[lane]);
                            *assembly << "EXIT;\n";
                        }
                        break;
                    case kIROp_IfElse:
                    case kIROp_Loop:
                    case kIROp_UnconditionalBranch:
                    case kIROp_FieldAddress:
                    case kIROp_GetElementPtr:
                        break;
                    case kIROp_Call:
                        {
                            auto invocation = as<IRCall>(inst);
                            auto callee = as<IRFunc>(invocation->getCallee());
                            auto body = callee ? callee->getFirstBlock() : nullptr;
                            auto generic = body ? as<IRGenericAsm>(body->getTerminator()) : nullptr;
                            auto name = generic ? as<IRStringLit>(generic->getOperand(0)) : nullptr;
                            bool sample = name && name->getStringSlice() == toSlice("nx2_sample");
                            if (sample && block != currentFunction->getFirstBlock())
                                reject(inst);
                            else
                            {
                                inConditionalEntryBlock = sample;
                                value(inst);
                                inConditionalEntryBlock = false;
                            }
                        }
                        break;
                    default:
                        value(inst);
                        break;
                    }
                    if (failed)
                        return;
                }
                emitConditionalRegion(simple->nextRegion, depth, outputCount);
            }
            break;
        case Region::Flavor::If:
            {
                auto conditional = static_cast<IfRegion*>(region);
                if (depth >= kNX2ReconvergenceBarrierCount)
                {
                    reject(conditional->ifElseInst);
                    return;
                }
                auto condition = value(conditional->getCondition());
                if (condition.getCount() != 1)
                {
                    reject(conditional->ifElseInst);
                    return;
                }
                auto predicate = reg(conditional->ifElseInst, condition[0]);
                auto thenBreak = conditional->thenRegion && conditional->thenRegion->getFlavor() ==
                                                                Region::Flavor::Break
                                     ? static_cast<BreakRegion*>(conditional->thenRegion.get())
                                     : nullptr;
                auto elseBreak = conditional->elseRegion && conditional->elseRegion->getFlavor() ==
                                                                Region::Flavor::Break
                                     ? static_cast<BreakRegion*>(conditional->elseRegion.get())
                                     : nullptr;
                if (thenBreak || elseBreak)
                {
                    auto branch = thenBreak ? thenBreak : elseBreak;
                    if (activeLoops.getCount() == 0 ||
                        branch->outerRegion != activeLoops.getLast().region ||
                        depth != activeLoops.getLast().depth + 1 || (thenBreak && elseBreak))
                    {
                        reject(conditional->ifElseInst);
                        return;
                    }
                    *assembly << "ISETP.NE.U32.AND P0, PT, " << operand(predicate) << ", RZ, PT;\n"
                              << (thenBreak ? "@P0 BRA " : "@!P0 BRA ") << "nx2_loop_sync_"
                              << activeLoops.getLast().label << ";\n";
                    emitConditionalRegion(
                        thenBreak ? conditional->elseRegion.get() : conditional->thenRegion.get(),
                        depth,
                        outputCount);
                    emitConditionalRegion(conditional->nextRegion, depth, outputCount);
                    break;
                }
                UInt label = nextLabel++;
                *assembly << "ISETP.NE.U32.AND P0, PT, " << operand(predicate)
                          << ", RZ, PT;\nBSSY B" << depth << ", nx2_done_" << label
                          << ";\n@!P0 BRA nx2_else_" << label << ";\n";
                emitConditionalRegion(conditional->thenRegion, depth + 1, outputCount);
                *assembly << "BRA nx2_merge_" << label << ";\nnx2_else_" << label << ":\n";
                emitConditionalRegion(conditional->elseRegion, depth + 1, outputCount);
                *assembly << "nx2_merge_" << label << ":\nBSYNC B" << depth << ";\nnx2_done_"
                          << label << ":\n";
                literalRegisters.clear();
                emitConditionalRegion(conditional->nextRegion, depth, outputCount);
            }
            break;
        case Region::Flavor::Loop:
            {
                auto loop = static_cast<LoopRegion*>(region);
                if (depth >= kNX2ReconvergenceBarrierCount)
                {
                    reject(loop->loopInst);
                    return;
                }
                UInt label = nextLabel++;
                activeLoops.add({loop, depth, label});
                *assembly << "BSSY B" << depth << ", nx2_loop_done_" << label
                          << ";\nnx2_loop_start_" << label << ":\n";
                emitConditionalRegion(loop->body, depth + 1, outputCount);
                *assembly << "BRA nx2_loop_start_" << label << ";\nnx2_loop_sync_" << label
                          << ":\nBSYNC B" << depth << ";\nnx2_loop_done_" << label << ":\n";
                activeLoops.removeLast();
                literalRegisters.clear();
                emitConditionalRegion(loop->nextRegion, depth, outputCount);
            }
            break;
        case Region::Flavor::Break:
        case Region::Flavor::Continue:
            {
                auto target = region->getFlavor() == Region::Flavor::Break
                                  ? static_cast<BreakableRegion*>(
                                        static_cast<BreakRegion*>(region)->outerRegion)
                                  : static_cast<BreakableRegion*>(
                                        static_cast<ContinueRegion*>(region)->outerRegion);
                if (activeLoops.getCount() == 0 || activeLoops.getLast().region != target ||
                    depth < activeLoops.getLast().depth + 1 ||
                    (region->getFlavor() == Region::Flavor::Continue &&
                     depth != activeLoops.getLast().depth + 1))
                {
                    reject(currentFunction);
                    return;
                }
                // BREAK removes transferring lanes from inner reconvergence barriers before
                // the branch leaves their regions, as in the pinned deep-control-flow capture.
                for (UInt barrier = depth; barrier-- > activeLoops.getLast().depth + 1;)
                    *assembly << "BREAK B" << barrier << ";\n";
                *assembly << "BRA nx2_loop_"
                          << (region->getFlavor() == Region::Flavor::Break ? "sync_" : "start_")
                          << activeLoops.getLast().label << ";\n";
            }
            break;
        default:
            reject(currentFunction);
            break;
        }
    }

    SlangResult emit(IRFunc* function)
    {
        currentFunction = function;
        auto block = function->getFirstBlock();
        auto layoutDecoration = function->findDecoration<IRLayoutDecoration>();
        auto layout =
            layoutDecoration ? as<IREntryPointLayout>(layoutDecoration->getLayout()) : nullptr;
        auto semantic = layout ? layout->getResultLayout()->findSystemValueSemanticAttr() : nullptr;
        UInt outputCount = width(function->getResultType());
        if (!block || !outputCount || outputCount > 4 || !semantic ||
            semantic->getName() != toSlice("SV_Target") || semantic->getIndex() != 0)
        {
            reject(function);
            return SLANG_FAIL;
        }
        *assembly << "// Experimental SM87 fragment assembly; modeled order, controls separate.\n";
        if (block->getNextBlock())
        {
            if (auto param = block->getFirstParam())
            {
                auto mode = param->findDecoration<IRInterpolationModeDecoration>();
                if (param->getNextParam() || nativeInterface != NX2Interface::PerspectiveTexture ||
                    getNX2VaryingSlot(param) != 0 || width(param->getDataType()) != 2 ||
                    (mode && mode->getMode() != IRInterpolationMode::Linear))
                {
                    reject(param);
                    return SLANG_FAIL;
                }
                // TEXCOORD0 uses the captured perspective interface; virtual registers keep
                // interpolation results live across control-flow joins without fixing R8/R9.
                auto reciprocal = allocate(param);
                *assembly << "IPA.PASS " << operand(reciprocal) << ", a[0x7c];\n"
                          << "MUFU.RCP " << operand(reciprocal) << ", " << operand(reciprocal)
                          << ";\n";
                List<NX2Operand> uv;
                for (UInt lane = 0; lane < 2; ++lane)
                {
                    auto interpolated = allocate(param);
                    *assembly << "IPA.PASS " << operand(interpolated) << ", a["
                              << StringUtil::makeStringWithFormat("0x%x", 0x80 + lane * 4)
                              << "];\n";
                    uv.add(binary(param, "FMUL.FTZ.RZ", reciprocal, interpolated));
                }
                values.add(param, uv);
            }
            for (auto current : function->getBlocks())
            {
                auto terminator = current->getTerminator();
                if (!terminator ||
                    (terminator->getOp() != kIROp_IfElse && terminator->getOp() != kIROp_Loop &&
                     terminator->getOp() != kIROp_UnconditionalBranch &&
                     terminator->getOp() != kIROp_Return))
                {
                    reject(terminator ? static_cast<IRInst*>(terminator) : function);
                    return SLANG_FAIL;
                }
            }
            auto regions = generateRegionTreeForFunc(function, sink);
            if (!regions || sink->getErrorCount())
                return SLANG_FAIL;
            emitConditionalRegion(regions->rootRegion, 0, outputCount);
            return failed ? SLANG_FAIL : SLANG_OK;
        }
        auto terminator = block->getTerminator();
        if (!terminator || terminator->getOp() != kIROp_Return ||
            terminator->getOperandCount() != 1)
        {
            reject(function);
            return SLANG_FAIL;
        }
        auto returned = terminator->getOperand(0);
        if (returned->getOp() == kIROp_MakeVector && returned->getOperandCount() == 2)
        {
            auto rgb = as<IRCall>(returned->getOperand(0));
            auto alpha = as<IRSwizzle>(returned->getOperand(1));
            bool safe = rgb && width(rgb->getDataType()) == 3 && alpha &&
                        alpha->getElementCount() == 1 &&
                        getIntVal(alpha->getElementIndex(0)) == 3 && as<IRCall>(alpha->getBase());
            if (safe)
            {
                for (auto next = rgb->getNextInst(); next; next = next->getNextInst())
                {
                    if (next != alpha && next != returned && next != terminator)
                        safe = false;
                }
            }
            if (safe)
            {
                for (UInt lane = 0; lane < 3; ++lane)
                    markOutput(rgb, lane, lane);
            }
        }
        auto firstParam = block->getFirstParam();
        auto interpolation =
            firstParam ? firstParam->findDecoration<IRInterpolationModeDecoration>() : nullptr;
        if (interpolation && interpolation->getMode() == IRInterpolationMode::NoPerspective)
        {
            for (auto param : block->getParams())
            {
                auto mode = param->findDecoration<IRInterpolationModeDecoration>();
                Int semanticIndex = getNX2VaryingSlot(param);
                UInt count = width(param->getDataType());
                if (!mode || mode->getMode() != IRInterpolationMode::NoPerspective ||
                    semanticIndex < 0 || !count || count > 4)
                {
                    reject(param);
                    return SLANG_FAIL;
                }
                List<NX2Operand> components;
                for (UInt lane = 0; lane < count; ++lane)
                {
                    auto component = allocate(param);
                    *assembly << "IPA.PASS " << operand(component) << ", a["
                              << StringUtil::makeStringWithFormat(
                                     "0x%x",
                                     UInt(0x80 + semanticIndex * 16 + lane * 4))
                              << "];\n";
                    components.add(component);
                }
                values.add(param, components);
            }
        }
        else if (auto param = firstParam)
        {
            for (auto decoration : param->getDecorations())
            {
                if (auto mode = as<IRInterpolationModeDecoration>(decoration);
                    mode && mode->getMode() != IRInterpolationMode::Linear)
                {
                    reject(param);
                    return SLANG_FAIL;
                }
            }
            auto decoration = param->findDecoration<IRSemanticDecoration>();
            Int semanticIndex = getNX2VaryingSlot(param);
            UInt count = width(param->getDataType());
            if (nativeInterface == NX2Interface::PerspectiveTexture && decoration &&
                semanticIndex >= 0 && count >= 1 && count <= 4 && !param->getNextParam() &&
                (count != 2 || semanticIndex != 0))
            {
                // Each varying occupies a four-component slot after reciprocal W.
                // For example, TEXCOORD1.x reads a[0x90], while TEXCOORD0.w reads a[0x8c].
                auto reciprocal = allocate(param);
                *assembly << "IPA.PASS " << operand(reciprocal) << ", a[0x7c];\n"
                          << "MUFU.RCP " << operand(reciprocal) << ", " << operand(reciprocal)
                          << ";\n";
                List<NX2Operand> components;
                for (UInt lane = 0; lane < count; ++lane)
                {
                    auto interpolated = allocate(param);
                    *assembly << "IPA.PASS " << operand(interpolated) << ", a["
                              << StringUtil::makeStringWithFormat(
                                     "0x%x",
                                     UInt(0x80 + semanticIndex * 16 + lane * 4))
                              << "];\n";
                    components.add(binary(param, "FMUL.FTZ.RZ", reciprocal, interpolated));
                }
                values.add(param, components);
            }
            else
            {
                auto expectedSemantic = nativeInterface == NX2Interface::ScreenTexture
                                            ? toSlice("SV_Position")
                                            : toSlice("TEXCOORD0");
                if (param->getNextParam() || width(param->getDataType()) != 2 || !decoration ||
                    cast<IRStringLit>(decoration->getOperand(0))->getStringSlice() !=
                        expectedSemantic)
                {
                    reject(param);
                    return SLANG_FAIL;
                }
                if (nativeInterface == NX2Interface::ScreenTexture)
                    *assembly << "IPA.PASS R8, a[0x70];\nIPA.PASS R9, a[0x74];\n";
                else
                    *assembly << "IPA.PASS R10, a[0x7c];\nIPA.PASS R8, a[0x80];\n"
                                 "IPA.PASS R9, a[0x84];\nMUFU.RCP R10, R10;\n"
                                 "FMUL.FTZ.RZ R8, R10, R8;\nFMUL.FTZ.RZ R9, R10, R9;\n";
                List<NX2Operand> uv;
                for (UInt lane = 0; lane < 2; ++lane)
                {
                    NX2Operand coordinate{NX2Operand::Kind::Register, 8 + lane};
                    if (nativeInterface == NX2Interface::ScreenTexture)
                    {
                        auto saved = allocate(param);
                        move(saved.index, coordinate);
                        coordinate = saved;
                    }
                    uv.add(coordinate);
                }
                values.add(param, uv);
            }
        }
        for (auto inst : block->getOrdinaryInsts())
        {
            switch (inst->getOp())
            {
            case kIROp_Return:
            case kIROp_IntLit:
            case kIROp_FieldAddress:
            case kIROp_GetElementPtr:
            case kIROp_MakeVector:
            case kIROp_Swizzle:
            case kIROp_Mul:
            case kIROp_Div:
            case kIROp_Load:
                break;
            default:
                value(inst);
                break;
            }
        }
        auto output = value(terminator->getOperand(0));
        if (failed || output.getCount() != Index(outputCount))
            return SLANG_FAIL;
        bool positiveZero = true;
        for (auto value : output)
        {
            uint32_t bits = 0;
            ::memcpy(&bits, &value.literal, sizeof(bits));
            if (value.kind != NX2Operand::Kind::Literal || bits != 0)
                positiveZero = false;
        }
        if (positiveZero && outputCount == 4)
        {
            *assembly << "CS2R R0, SRZ;\nCS2R R2, SRZ;\nEXIT;\n";
            return SLANG_OK;
        }
        bool needsParallelCopy = false;
        for (UInt lane = 0; lane < outputCount; ++lane)
        {
            if (output[lane].absolute && output[lane].kind != NX2Operand::Kind::Literal)
                reject(terminator);
            if (output[lane].kind == NX2Operand::Kind::Register && output[lane].index < 4 &&
                output[lane].index != lane)
                needsParallelCopy = true;
        }
        if (failed)
            return SLANG_FAIL;
        if (needsParallelCopy)
        {
            for (UInt lane = 0; lane < outputCount; ++lane)
            {
                move(4 + lane, output[lane]);
                output[lane] = {NX2Operand::Kind::Register, 4 + lane};
            }
        }
        for (UInt lane = 0; lane < outputCount; ++lane)
            move(lane, output[lane]);
        *assembly << "EXIT;\n";
        return failed ? SLANG_FAIL : SLANG_OK;
    }
};
} // namespace

SlangResult emitNX2Assembly(
    IRFunc* entryPoint,
    DiagnosticSink* sink,
    bool sceneTextureABI,
    StringBuilder* assembly)
{
    StringBuilder virtualAssembly;
    // The bounded NX2 interface uses perspective TEXCOORD0 or screen SV_Position.
    // These are shader input semantics, not separate target capabilities.
    NX2Interface nativeInterface = NX2Interface::PerspectiveTexture;
    if (auto block = entryPoint->getFirstBlock())
    {
        if (auto param = block->getFirstParam())
        {
            if (auto semantic = param->findDecoration<IRSemanticDecoration>())
            {
                if (cast<IRStringLit>(semantic->getOperand(0))->getStringSlice() ==
                    toSlice("SV_Position"))
                    nativeInterface = NX2Interface::ScreenTexture;
            }
        }
    }
    NX2Emitter emitter{sink, &virtualAssembly, nativeInterface, sceneTextureABI};
    SLANG_RETURN_ON_FAIL(emitter.emit(entryPoint));
    if (entryPoint->getFirstBlock()->getNextBlock())
        return allocateNX2ConditionalRegisters(
            virtualAssembly.toString(),
            emitter.nextRegister,
            emitter.width(entryPoint->getResultType()),
            sink,
            assembly);
    return allocateNX2Registers(
        virtualAssembly.toString(),
        sink,
        emitter.width(entryPoint->getResultType()),
        assembly);
}
} // namespace Slang