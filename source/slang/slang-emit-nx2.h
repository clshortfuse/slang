#pragma once

#include "slang-ir.h"

namespace Slang
{
class DiagnosticSink;

SlangResult emitNX2Assembly(
    IRFunc* entryPoint,
    DiagnosticSink* sink,
    StringBuilder* assembly);
} // namespace Slang