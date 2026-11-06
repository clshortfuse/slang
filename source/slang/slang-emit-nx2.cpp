#include "slang-emit-nx2.h"

#include "core/slang-string-util.h"
#include "slang-diagnostics.h"
#include "slang-ir-insts.h"
#include "slang-ir-util.h"

namespace Slang
{
namespace
{
enum class NX2Interface
{
    PerspectiveTexture,
    ScreenTexture
};

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
    StringBuilder* output)
{
    List<NX2ScheduledInstruction> program;
    Index lastWrite[12];
    List<Index> readers[12];
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
            for (UInt number = 0; number < 4; ++number)
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
        else
        {
            writes.add(registers[0]);
            for (Index index = 1; index < registers.getCount(); ++index)
                reads.add(registers[index]);
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
SlangResult allocateNX2Registers(const String& input, DiagnosticSink* sink, StringBuilder* output)
{
    List<NX2NativeLine> lines;
    List<NX2LiveInterval> intervals;
    Index current[255];
    for (auto& interval : current)
        interval = -1;
    bool valid = true;
    Index instruction = 0;
    auto read = [&](UInt number, Index position)
    {
        if (number >= 255 || current[number] < 0)
        {
            valid = false;
            return Index(-1);
        }
        intervals[current[number]].end = position;
        return current[number];
    };
    auto write = [&](UInt number, Index position)
    {
        if (number >= 255)
        {
            valid = false;
            return Index(-1);
        }
        Index index = intervals.getCount();
        intervals.add({position, position, number, number < 11 ? number : UInt(255)});
        current[number] = index;
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
            for (UInt number = 0; number < 4; ++number)
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
        if (interval.physicalRegister < 12)
            candidates.add(interval.physicalRegister);
        else
        {
            UInt preferred = interval.preferredSource >= 0
                                 ? intervals[interval.preferredSource].physicalRegister
                                 : 255;
            if (preferred < 12)
                candidates.add(preferred);
            for (UInt number = 0; number < 12; ++number)
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
                           "twelve registers",
                .location = SourceLoc()});
        return SLANG_FAIL;
    }
    scheduleNX2Lines(lines, intervals, output);
    return SLANG_OK;
}

struct NX2Operand
{
    enum class Kind
    {
        Register,
        Literal,
        ConstantBuffer
    };
    Kind kind = Kind::Register;
    UInt index = 0;
    float literal = 0;
    bool absolute = false;
};

struct NX2Emitter
{
    DiagnosticSink* sink;
    StringBuilder* assembly;
    NX2Interface nativeInterface;
    bool failed = false;
    bool sampled = false;
    UInt nextRegister = 11;
    Dictionary<IRInst*, List<NX2Operand>> values;
    Dictionary<uint32_t, NX2Operand> literalRegisters;
    Dictionary<IRInst*, List<UInt>> outputLocations;

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
        if (value.kind == NX2Operand::Kind::Literal)
        {
            uint32_t bits = 0;
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

    NX2Operand allocate(IRInst* inst)
    {
        if (nextRegister >= 255)
            reject(inst);
        return {NX2Operand::Kind::Register, nextRegister++};
    }

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
        if (name == toSlice("nx2_sample"))
        {
            auto texture = inst->getArgCount() == 3
                               ? as<IRTextureTypeBase>(inst->getArg(0)->getDataType())
                               : nullptr;
            if (sampled || inst->getArgCount() != 3 || !texture ||
                texture->getShape() != SLANG_TEXTURE_2D || texture->isMultisample() ||
                texture->isShadow() || texture->isCombined() ||
                texture->getAccess() != SLANG_RESOURCE_ACCESS_READ ||
                width(texture->getElementType()) != 4 ||
                !binding(inst->getArg(0), LayoutResourceKind::ShaderResource, 0) ||
                !binding(inst->getArg(1), LayoutResourceKind::SamplerState, 0) ||
                width(inst->getDataType()) != 4)
            {
                reject(inst);
                return result;
            }
            auto uv = value(inst->getArg(2));
            if (uv.getCount() != 2 || uv[0].kind != NX2Operand::Kind::Register ||
                uv[1].kind != NX2Operand::Kind::Register ||
                (nativeInterface == NX2Interface::PerspectiveTexture &&
                 (uv[0].index != 8 || uv[1].index != 9)))
            {
                reject(inst);
                return result;
            }
            if (nativeInterface == NX2Interface::ScreenTexture)
            {
                move(8, uv[0]);
                move(9, uv[1]);
            }
            sampled = true;
            *assembly << "TEX.SCR.NODEP R2, R0, R8, R9, 0x2, 0x8, 2D;\n";
            for (UInt lane = 0; lane < 4; ++lane)
                result.add({NX2Operand::Kind::Register, lane});
            return result;
        }
        if (inst->getArgCount() == 0)
        {
            reject(inst);
            return result;
        }
        auto a = value(inst->getArg(0));
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
                *assembly << "FADD.FTZ " << operand(difference) << ", " << operand(end)
                          << ", -" << operand(start) << ";\n";
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
                *assembly << "FADD.FTZ.SAT " << operand(destination) << ", RZ, "
                          << operand(source) << ";\n";
                result.add(destination);
            }
            return result;
        }
        if ((name == toSlice("nx2_min") || name == toSlice("nx2_max")) &&
            inst->getArgCount() == 2)
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
                *assembly << "FMNMX.FTZ " << operand(destination) << ", " << operand(source)
                          << ", " << operand(b[lane])
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
            else if (name == toSlice("nx2_log2") || name == toSlice("nx2_exp2"))
            {
                source = reg(inst, source);
                auto destination = allocate(inst);
                if (auto locations = outputLocations.tryGetValue(inst))
                {
                    if (canWriteOutputBank && (*locations)[lane] < 4)
                        destination.index = (*locations)[lane];
                }
                *assembly << (name == toSlice("nx2_log2") ? "MUFU.LG2 " : "MUFU.EX2 ")
                          << operand(destination) << ", " << operand(source) << ";\n";
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
        else if (inst->getOp() == kIROp_MakeVector)
        {
            for (UInt index = 0; index < inst->getOperandCount(); ++index)
                result.addRange(value(inst->getOperand(index)));
        }
        else if (inst->getOp() == kIROp_Load)
            result = load(inst);
        else if (auto invocation = as<IRCall>(inst))
            result = call(invocation);
        else if (
            inst->getOp() == kIROp_Mul || inst->getOp() == kIROp_Add || inst->getOp() == kIROp_Div)
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

    SlangResult emit(IRFunc* function)
    {
        auto block = function->getFirstBlock();
        auto layoutDecoration = function->findDecoration<IRLayoutDecoration>();
        auto layout =
            layoutDecoration ? as<IREntryPointLayout>(layoutDecoration->getLayout()) : nullptr;
        auto semantic = layout ? layout->getResultLayout()->findSystemValueSemanticAttr() : nullptr;
        if (!block || block->getNextBlock() || width(function->getResultType()) != 4 || !semantic ||
            semantic->getName() != toSlice("SV_Target") || semantic->getIndex() != 0)
        {
            reject(function);
            return SLANG_FAIL;
        }
        *assembly << "// Experimental SM87 fragment assembly; modeled order, controls separate.\n";
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
        if (auto param = block->getFirstParam())
        {
            auto decoration = param->findDecoration<IRSemanticDecoration>();
            auto expectedSemantic = nativeInterface == NX2Interface::ScreenTexture
                                        ? toSlice("SV_Position")
                                        : toSlice("TEXCOORD0");
            if (param->getNextParam() ||
                width(param->getDataType()) != 2 || !decoration ||
                cast<IRStringLit>(decoration->getOperand(0))->getStringSlice() != expectedSemantic)
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
        for (auto inst : block->getOrdinaryInsts())
        {
            switch (inst->getOp())
            {
            case kIROp_Return:
            case kIROp_FieldAddress:
            case kIROp_GetElementPtr:
            case kIROp_MakeVector:
            case kIROp_Swizzle:
            case kIROp_Mul:
            case kIROp_Add:
            case kIROp_Div:
            case kIROp_Load:
                break;
            default:
                value(inst);
                break;
            }
        }
        auto output = value(terminator->getOperand(0));
        if (failed || output.getCount() != 4)
            return SLANG_FAIL;
        bool positiveZero = true;
        for (auto value : output)
        {
            uint32_t bits = 0;
            ::memcpy(&bits, &value.literal, sizeof(bits));
            if (value.kind != NX2Operand::Kind::Literal || bits != 0)
                positiveZero = false;
        }
        if (positiveZero)
        {
            *assembly << "CS2R R0, SRZ;\nCS2R R2, SRZ;\nEXIT;\n";
            return SLANG_OK;
        }
        bool needsParallelCopy = false;
        for (UInt lane = 0; lane < 4; ++lane)
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
            for (UInt lane = 0; lane < 4; ++lane)
            {
                move(4 + lane, output[lane]);
                output[lane] = {NX2Operand::Kind::Register, 4 + lane};
            }
        }
        for (UInt lane = 0; lane < 4; ++lane)
            move(lane, output[lane]);
        *assembly << "EXIT;\n";
        return failed ? SLANG_FAIL : SLANG_OK;
    }
};
} // namespace

SlangResult emitNX2Assembly(
    IRFunc* entryPoint,
    DiagnosticSink* sink,
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
    NX2Emitter emitter{sink, &virtualAssembly, nativeInterface};
    SLANG_RETURN_ON_FAIL(emitter.emit(entryPoint));
    return allocateNX2Registers(virtualAssembly.toString(), sink, assembly);
}
} // namespace Slang