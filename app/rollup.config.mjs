import typescript from "rollup-plugin-ts";
import commonjs from '@rollup/plugin-commonjs';
import { nodeResolve } from '@rollup/plugin-node-resolve';
import {lezer} from "@lezer/generator/rollup";

export default {
  input: "./client/editor.mjs",
  output: [
    {
      file: "./www/static/editor.bundle.js", 
      format: "iife", 
      name:"MyBundle"
    }
  ],
  plugins: [lezer(), typescript(), nodeResolve(),
    commonjs({include:'node_modules/**',
              requireReturnsDefault: 'auto'
    })]
}
