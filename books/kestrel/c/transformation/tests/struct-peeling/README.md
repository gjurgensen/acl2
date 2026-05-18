# Struct Peeling Test Cases

This directory contains test cases for the struct peeling transformation, which splits a struct into two separate structs by moving some fields to a new struct type.

## Test Files

### Basic Tests
- **simple-split.c**: Simplest possible case - splitting a 2-field struct
- **test1.c**: Basic struct peeling with a Point struct (position + color)
- **test2.c**: Struct with designated initializers
- **test3.c**: Multiple instances of the same struct type

### Member Access
- **mixed-access.c**: Mixed access patterns to fields in both groups
- **pointer-access.c**: Pointer member access using -> operator (memberp)

### Function-Related
- **test4.c**: Functions taking struct as parameter
- **return-value.c**: Functions returning struct values
- **multiple-functions.c**: Multiple functions accessing different fields

### Scoping
- **global-and-local.c**: Both global and local struct variables

### Initializers
- **designated-init.c**: Various designated initializer patterns

### Edge Cases / Potentially Illegal
- **array-of-structs.c**: Arrays of structs (marked as illegal in design)
- **nested-structs.c**: Nested struct definitions (derivative types)
- **self-reference.c**: Self-referencing structs (marked as illegal in design)

## Transformation Strategy

Based on the design notes, the transformation should:

1. **Split the struct declaration**: Original struct keeps some fields, new struct gets others
2. **Split object declarations**: Each `struct Foo x;` becomes two declarations
3. **Split initializers**: Designated initializers are distributed to appropriate struct
4. **Rewrite member access**: `obj.field` uses correct split object
5. **Rewrite pointer access**: `ptr->field` uses correct split pointer
6. **Transform function parameters**: `func(struct Foo x)` becomes `func(struct Foo x, struct FooNew y)`
7. **Transform function calls**: Arguments are duplicated/split appropriately

## Suggested Split Groups

Each test file has comments suggesting a logical split. For example:
- **test1.c**: Split into position (x,y) and color (r,g,b)
- **test2.c**: Split into personal (id,age) and employment (salary,years_employed)
- **test4.c**: Split into position (x,y) and dimensions (width,height)

These splits represent common use cases like separating hot/cold data or grouping related fields.
