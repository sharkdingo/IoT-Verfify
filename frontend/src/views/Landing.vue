<script setup lang="ts">
import { ref, onMounted, onUnmounted } from 'vue';
import { useRouter } from 'vue-router';

const router = useRouter();

const goToLogin = () => {
  router.push('/login');
};

const mouseX = ref(0);
const mouseY = ref(0);

const handleMouseMove = (e: MouseEvent) => {
  const x = (e.clientX / window.innerWidth - 0.5) * 2;
  const y = (e.clientY / window.innerHeight - 0.5) * 2;
  mouseX.value = x;
  mouseY.value = y;
};

onMounted(() => {
  window.addEventListener('mousemove', handleMouseMove);
});

onUnmounted(() => {
  window.removeEventListener('mousemove', handleMouseMove);
});
</script>

<template>
  <div 
    class="landing-wrapper"
    :style="{
      '--mouse-x': mouseX,
      '--mouse-y': mouseY
    }"
  >
    <!-- Video Background -->
    <video
      class="video-bg"
      autoplay
      loop
      muted
      playsinline
      poster="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 1920 1080'%3E%3Crect fill='%2320121a' width='1920' height='1080'/%3E%3C/svg%3E"
    >
      <source src="https://cdn.pixabay.com/video/2025/05/06/277096_large.mp4" type="video/mp4">
    </video>

    <!-- Dark Overlay -->
    <div class="video-overlay"></div>

    <!-- Navigation -->
    <nav class="nav-bar">
      <div class="nav-content">
        <div class="logo">
          IoT-Verify<sup class="logo-sup">®</sup>
        </div>
        
        <div class="nav-links">
          <a href="#" class="nav-link active">Devices</a>
          <a href="#" class="nav-link">Automation</a>
          <a href="#" class="nav-link">Templates</a>
          <a href="#" class="nav-link">Rules</a>
        </div>

        <button class="cta-button liquid-glass" @click="goToLogin">
          Get Started
        </button>
      </div>
    </nav>

    <!-- Hero Section -->
    <section class="hero-section">
      <h1 class="hero-title animate-fade-rise">
        Orchestrate your <em class="emphasis">intelligent space</em> with visual precision.
      </h1>
      
      <p class="hero-subtext animate-fade-rise-delay">
        Design, connect, and automate your IoT ecosystem through an intuitive canvas. 
        Build complex device rules with  visual logic — no coding required.
      </p>
      
      <button class="hero-cta liquid-glass animate-fade-rise-delay-2" @click="goToLogin">
        Get Started
      </button>
    </section>
  </div>
</template>

<style>
/* CSS Variables - Dark Theme */
:root {
  --background: 201 100% 13%;
  --foreground: 0 0% 100%;
  --muted-foreground: 240 4% 66%;
  --primary: 0 0% 100%;
  --primary-foreground: 0 0% 4%;
  --secondary: 0 0% 10%;
  --muted: 0 0% 10%;
  --accent: 0 0% 10%;
  --border: 0 0% 18%;
  --input: 0 0% 18%;
  
  --font-display: 'Instrument Serif', serif;
  --font-body: 'Inter', sans-serif;
}

/* Import Fonts */
@import url('https://fonts.googleapis.com/css2?family=Instrument+Serif:ital@0;1&family=Inter:wght@400;500&display=swap');

/* Reset & Base */
* {
  margin: 0;
  padding: 0;
  box-sizing: border-box;
}

.landing-wrapper {
  position: relative;
  width: 100%;
  height: 100vh;
  overflow: hidden;
  background-color: hsl(201, 100%, 13%);
  font-family: var(--font-body);
  color: hsl(0, 0%, 100%);
}

/* Video Background */
.video-bg {
  position: absolute;
  top: calc(var(--mouse-y) * 10px);
  left: calc(var(--mouse-x) * 10px);
  width: calc(100% + 20px);
  height: calc(100% + 20px);
  object-fit: cover;
  z-index: 0;
  transition: transform 0.1s ease-out;
}

/* Video Overlay */
.video-overlay {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: linear-gradient(
    135deg,
    rgba(10, 20, 35, 0.7) 0%,
    rgba(20, 30, 50, 0.5) 50%,
    rgba(10, 20, 35, 0.7) 100%
  );
  z-index: 1;
}

/* Navigation Bar */
.nav-bar {
  position: relative;
  z-index: 10;
  display: flex;
  justify-content: center;
  padding: 1.5rem 2rem;
}

.nav-content {
  display: flex;
  flex-direction: row;
  justify-content: space-between;
  align-items: center;
  width: 100%;
  padding: 0 2rem;
}

.logo {
  font-family: var(--font-display);
  font-size: 1.875rem;
  letter-spacing: -0.025em;
  color: hsl(0, 0%, 100%);
}

.logo-sup {
  font-size: 0.75rem;
  vertical-align: super;
}

.nav-links {
  display: flex;
  gap: 2rem;
}

@media (max-width: 767px) {
  .nav-links {
    display: none;
  }
}

.nav-link {
  font-size: 0.875rem;
  color: hsl(0, 0%, 80%);
  text-decoration: none;
  transition: color 0.2s, text-shadow 0.2s;
}

.nav-link:hover {
  color: hsl(0, 0%, 100%);
  text-shadow: 0 0 10px rgba(255, 255, 255, 0.5);
}

.nav-link.active {
  color: hsl(0, 0%, 100%);
  text-shadow: 0 0 10px rgba(255, 255, 255, 0.3);
}

/* CTA Button - Liquid Glass */
.liquid-glass {
  background: rgba(255, 255, 255, 0.01);
  background-blend-mode: luminosity;
  backdrop-filter: blur(4px);
  -webkit-backdrop-filter: blur(4px);
  border: none;
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.1);
  position: relative;
  overflow: hidden;
  border-radius: 9999px;
  padding: 0.625rem 1.5rem;
  font-size: 0.875rem;
  color: hsl(0, 0%, 100%);
  cursor: pointer;
  transition: transform 0.2s;
}

.liquid-glass:hover {
  transform: scale(1.03);
}

.liquid-glass::before {
  content: '';
  position: absolute;
  top: 0;
  right: 0;
  bottom: 0;
  left: 0;
  border-radius: inherit;
  padding: 1.4px;
  background: linear-gradient(180deg, rgba(255,255,255,0.45) 0%, rgba(255,255,255,0.15) 20%, rgba(255,255,255,0) 40%, rgba(255,255,255,0) 60%, rgba(255,255,255,0.15) 80%, rgba(255,255,255,0.45) 100%);
  -webkit-mask: linear-gradient(#fff 0 0) content-box, linear-gradient(#fff 0 0);
  -webkit-mask-composite: xor;
  mask-composite: exclude;
  pointer-events: none;
}

/* Hero Section */
.hero-section {
  position: relative;
  z-index: 10;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  text-align: center;
  padding: 2rem 1.5rem;
  padding-top: 8rem;
  padding-bottom: 10rem;
  min-height: calc(100vh - 100px);
}

.hero-title {
  font-family: var(--font-display);
  font-size: 3rem;
  font-weight: 400;
  line-height: 0.95;
  letter-spacing: -0.0615rem;
  max-width: 56rem;
  color: hsl(0, 0%, 100%);
  text-shadow: 0 4px 20px rgba(0, 0, 0, 0.6);
}

@media (min-width: 640px) {
  .hero-title {
    font-size: 4.5rem;
  }
}

@media (min-width: 768px) {
  .hero-title {
    font-size: 5rem;
  }
}

.emphasis {
  color: hsl(210, 100%, 70%);
  font-style: normal;
  text-shadow: 0 0 30px rgba(100, 200, 255, 0.4);
}

.hero-subtext {
  font-size: 1rem;
  color: hsl(0, 0%, 85%);
  max-width: 42rem;
  margin-top: 2rem;
  line-height: 1.625;
  text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5);
}

@media (min-width: 640px) {
  .hero-subtext {
    font-size: 1.125rem;
  }
}

.hero-cta {
  background: rgba(255, 255, 255, 0.01);
  background-blend-mode: luminosity;
  backdrop-filter: blur(4px);
  -webkit-backdrop-filter: blur(4px);
  border: none;
  box-shadow: inset 0 1px 1px rgba(255, 255, 255, 0.1);
  position: relative;
  overflow: hidden;
  border-radius: 9999px;
  padding: 1.25rem 3.5rem;
  font-size: 1rem;
  color: hsl(0, 0%, 100%);
  cursor: pointer;
  transition: transform 0.2s;
  margin-top: 3rem;
}

.hero-cta:hover {
  transform: scale(1.03);
}

.hero-cta::before {
  content: '';
  position: absolute;
  top: 0;
  right: 0;
  bottom: 0;
  left: 0;
  border-radius: inherit;
  padding: 1.4px;
  background: linear-gradient(180deg, rgba(255,255,255,0.45) 0%, rgba(255,255,255,0.15) 20%, rgba(255,255,255,0) 40%, rgba(255,255,255,0) 60%, rgba(255,255,255,0.15) 80%, rgba(255,255,255,0.45) 100%);
  -webkit-mask: linear-gradient(#fff 0 0) content-box, linear-gradient(#fff 0 0);
  -webkit-mask-composite: xor;
  mask-composite: exclude;
  pointer-events: none;
}

/* Animations */
@keyframes fade-rise {
  from {
    opacity: 0;
    transform: translateY(24px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.animate-fade-rise {
  animation: fade-rise 0.8s ease-out both;
}

.animate-fade-rise-delay {
  animation: fade-rise 0.8s ease-out 0.2s both;
}

.animate-fade-rise-delay-2 {
  animation: fade-rise 0.8s ease-out 0.4s both;
}

/* Mobile responsive */
@media (max-width: 767px) {
  .hero-title {
    font-size: 2.5rem;
    letter-spacing: -0.02rem;
  }
}
</style>