#version 450

void foo(out float bar, inout float baz, in float a, float b) {
    baz += 2.0f;
    bar = baz;
}

void main() {
    float bar = 0.0f;
    float baz = 0.0f;
    float a = 5.0f;
    foo(bar, baz, a, 5.0f);
}
