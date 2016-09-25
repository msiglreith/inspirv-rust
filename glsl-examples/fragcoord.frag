#version 450

in vec4 gl_FragCoord;
layout(location=0) out vec4 color;

void main() {
    vec4 c = gl_FragCoord;
    c.w = 1.0f;
    color = c;
}