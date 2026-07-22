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
        primary: "#6366f1",
        secondary: "#C026D3",
      },
      fontFamily: {
        display: ["Space Grotesk Variable", "Space Grotesk", "sans-serif"],
        body: ["Inter Variable", "Inter", "sans-serif"],
      },
      borderRadius: {
        DEFAULT: "0.75rem",
        '2xl': '1.5rem',
        '3xl': '2rem',
      },
    },
  },
  plugins: [],
}
