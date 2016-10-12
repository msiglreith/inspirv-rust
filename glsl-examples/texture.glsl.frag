#version 450

uniform sampler s;
uniform texture2D t;
uniform sampler2D ts;

void main() {
    vec4 color = texture(sampler2D(t, s), vec2(1.0, 1.0));
}