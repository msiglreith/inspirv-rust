#version 450

struct B { float a; };

layout(set = 0, binding = 0) uniform Block {
    vec2 a;
    B b;
    mat4 c;
} test;

void main() {}