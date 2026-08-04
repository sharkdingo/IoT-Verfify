/** @type {import('tailwindcss').Config} */
export default {
  darkMode: 'class',
  content: [
    "./index.html",
    "./src/**/*.{vue,js,ts,jsx,tsx}",
  ],
  theme: {
    extend: {
      colors: {
        // Single source of truth lives in styles/base.css so Tailwind utilities and
        // hand-written CSS cannot drift into two different "primary" colors.
        //
        // Because this is an arbitrary `var()` and not a channel triple, Tailwind cannot derive an
        // alpha channel from it: opacity modifiers like `border-primary/20` do NOT work and silently
        // render at full strength. For a translucent accent use
        // `color-mix(in srgb, var(--iot-color-accent) N%, transparent)`.
        primary: "var(--iot-color-accent)",
      },
      borderRadius: {
        DEFAULT: "0.75rem",
        '2xl': '1.5rem',
      },
    },
  },
  plugins: [],
}
