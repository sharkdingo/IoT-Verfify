package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzInputEventDto;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.SplittableRandom;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PaperEventDomainTest {

    @Test
    void eventAndSeedEnforcePaperPositionAndImmutabilityRules() {
        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.DEVICE, "thermostat", "heat", 2));
        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "21", 0));

        PaperEvent later = new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "21", 3);
        PaperEvent earlier = new PaperEvent(
                PaperEvent.Type.DEVICE, "thermostat", "heat", 1);
        List<PaperEvent> mutableEvents = new ArrayList<>(List.of(later, earlier));
        PaperInitialValue override = new PaperInitialValue(
                PaperInitialValue.Type.DEVICE_STATE,
                "thermostat",
                "mode",
                "heat");
        List<PaperInitialValue> mutableOverrides = new ArrayList<>(List.of(override));
        PaperSeed seed = new PaperSeed(73L, mutableOverrides, mutableEvents);
        mutableEvents.clear();
        mutableOverrides.clear();

        assertEquals(73L, seed.initializationNonce());
        assertEquals(List.of(override), seed.initialOverrides());
        assertEquals(List.of(earlier, later), seed.events());
        assertThrows(UnsupportedOperationException.class,
                () -> seed.initialOverrides().add(override));
        assertThrows(UnsupportedOperationException.class, () -> seed.events().add(earlier));
        assertThrows(IllegalArgumentException.class, () -> new PaperSeed(1L, List.of(
                later,
                new PaperEvent(PaperEvent.Type.ENVIRONMENT, "temperature", "18", 3))));
        assertThrows(IllegalArgumentException.class, () -> new PaperSeed(
                1L,
                List.of(override, new PaperInitialValue(
                        PaperInitialValue.Type.DEVICE_STATE,
                        "thermostat",
                        "mode",
                        "off")),
                List.of()));
    }

    @Test
    void seedEventMapsLosslesslyWithKindAndProvenance() {
        PaperEventDomainSnapshot domain = domain();

        FuzzInputEventDto device = new PaperEvent(
                PaperEvent.Type.DEVICE, "thermostat", "heat", 1)
                .toFuzzInputEventDto(domain);
        assertEquals(0, device.getStep());
        assertEquals("DEVICE_STATE", device.getKind());
        assertEquals("thermostat", device.getTargetId());
        assertEquals("mode", device.getProperty());
        assertEquals("heat", device.getValue());
        assertEquals("SEED_EVENT", device.getSource());

        FuzzInputEventDto environment = new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "rate:1", 3)
                .toFuzzInputEventDto(domain);
        assertEquals(2, environment.getStep());
        assertEquals("ENVIRONMENT_RATE", environment.getKind());
        assertEquals("environment", environment.getTargetId());
        assertEquals("temperature", environment.getProperty());
        assertEquals("rate:1", environment.getValue());
        assertEquals("SEED_EVENT", environment.getSource());

        PaperEnvironmentDomain discreteDomain = new PaperEnvironmentDomain(
                "door", "environment", "doorState", List.of("open", "closed"), List.of());
        PaperEventDomainSnapshot domainWithDiscrete = new PaperEventDomainSnapshot(
                5, domain.deviceDomains(), List.of(discreteDomain));
        FuzzInputEventDto discrete = new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "door", "open", 2)
                .toFuzzInputEventDto(domainWithDiscrete);
        assertEquals("ENVIRONMENT_VALUE", discrete.getKind());
        assertEquals("SEED_EVENT", discrete.getSource());

        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "not-legal", 2)
                .toFuzzInputEventDto(domain));
        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "18", 2)
                .toFuzzInputEventDto(domain));
        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "18", 6)
                .toFuzzInputEventDto(domain));
    }

    @Test
    void initializationIsDeterministicAndUsesDirectEnvironmentValuesOnly() {
        PaperEventDomainSnapshot domain = domain();

        List<PaperEvent> first = domain.materializeInitialState(8128L);
        List<PaperEvent> repeated = domain.materializeInitialState(8128L);

        assertEquals(first, repeated);
        assertEquals(2, first.size());
        PaperEvent device = eventOfType(first, PaperEvent.Type.DEVICE);
        PaperEvent environment = eventOfType(first, PaperEvent.Type.ENVIRONMENT);
        assertEquals(1, device.position());
        assertTrue(List.of("off", "heat").contains(device.value()));
        assertEquals(1, environment.position());
        assertTrue(List.of("18", "21").contains(environment.value()));
        assertEquals(List.of("rate:-1", "rate:1"),
                domain.environment("temperature").eventValues());
        assertEquals(List.of("18", "21"), domain.environment("temperature").initialStateValues());
    }

    @Test
    void initializationIncludesDeviceLocalVariablesInAReproducibleBaseline() {
        PaperInitialValueDomain local = PaperInitialValueDomain.enumerated(
                PaperInitialValue.Type.DEVICE_VARIABLE,
                "thermostat",
                "profile",
                List.of("eco", "comfort"));
        PaperEventDomainSnapshot domain = new PaperEventDomainSnapshot(
                5,
                domain().deviceDomains(),
                domain().environmentDomains(),
                List.of(local));

        List<PaperInitialValue> first = domain.materializeInitialValues(8128L);
        List<PaperInitialValue> repeated = domain.materializeInitialValues(8128L);

        assertEquals(first, repeated);
        assertEquals(3, first.size());
        assertEquals(List.of(
                        PaperInitialValue.Type.DEVICE_STATE,
                        PaperInitialValue.Type.ENVIRONMENT_VALUE,
                        PaperInitialValue.Type.DEVICE_VARIABLE),
                first.stream().map(PaperInitialValue::type).toList());
        assertTrue(List.of("eco", "comfort").contains(first.get(2).value()));
    }

    @Test
    void discreteEnvironmentValuesCanBeUsedAsEventsWhenNoRateDomainExists() {
        PaperEnvironmentDomain discrete = new PaperEnvironmentDomain(
                "door", "environment", "doorState", List.of("open", "closed"), List.of());

        assertEquals(List.of("open", "closed"), discrete.eventValues());
        assertEquals(List.of("open", "closed"), discrete.initialStateValues());
    }

    @Test
    void numericRangesRemainCompleteWithoutEnumeratingEveryInteger() {
        PaperEnvironmentDomain numeric = PaperEnvironmentDomain.numeric(
                "temperature",
                "environment",
                "temperature",
                -2_000_000_000,
                2_000_000_000,
                -20_000,
                20_000);
        PaperEventDomainSnapshot domain = new PaperEventDomainSnapshot(
                3, List.of(), List.of(numeric));

        assertTrue(numeric.initialStateValues().isEmpty());
        assertTrue(numeric.eventValues().isEmpty());
        assertTrue(numeric.isValidInitialValue("1379"));
        assertTrue(numeric.isValidEventValue("rate:1379"));
        assertEquals("ENVIRONMENT_RATE", new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "rate:1379", 2)
                .toFuzzInputEventDto(domain).getKind());
        assertTrue(numeric.isValidInitialValue(
                domain.materializeInitialState(19L).get(0).value()));
        String changed = numeric.differentEventValue(
                new SplittableRandom(7L), "rate:1379");
        assertNotEquals("rate:1379", changed);
        assertTrue(numeric.isValidEventValue(changed));
        assertThrows(IllegalArgumentException.class, () -> new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "1379", 2)
                .toFuzzInputEventDto(domain));
    }

    @Test
    void numericDirectValueDomainReportsWhetherModificationCanChangeTheValue() {
        PaperEnvironmentDomain singleValue = new PaperEnvironmentDomain(
                "level", "environment", "level", List.of(), List.of(),
                7, 7, null, null);
        PaperEnvironmentDomain multipleValues = new PaperEnvironmentDomain(
                "level", "environment", "level", List.of(), List.of(),
                7, 9, null, null);

        assertFalse(singleValue.hasAlternativeEventValue("7"));
        assertTrue(multipleValues.hasAlternativeEventValue("7"));
        assertNotEquals(
                "7",
                multipleValues.differentEventValue(new SplittableRandom(17L), "7"));
    }

    @Test
    void domainsRejectUnboundedOrAmbiguousInputs() {
        assertThrows(IllegalArgumentException.class, () -> new PaperEventDomainSnapshot(
                0, List.of(new PaperDeviceDomain("d", "mode", List.of("off"))), List.of()));
        assertThrows(IllegalArgumentException.class, () -> new PaperEventDomainSnapshot(
                PaperEventDomain.MAX_TRACE_LENGTH + 1,
                List.of(new PaperDeviceDomain("d", "mode", List.of("off"))),
                List.of()));
        assertThrows(IllegalArgumentException.class, () -> new PaperEventDomainSnapshot(
                1, List.of(), List.of()));
        assertThrows(IllegalArgumentException.class, () -> new PaperEventDomainSnapshot(
                1,
                List.of(
                        new PaperDeviceDomain("d", "mode", List.of("off")),
                        new PaperDeviceDomain("d", "power", List.of("on"))),
                List.of()));

        List<String> tooManyValues = IntStream.rangeClosed(
                        0, PaperEventDomain.MAX_VALUES_PER_TARGET)
                .mapToObj(Integer::toString)
                .toList();
        assertThrows(IllegalArgumentException.class, () -> new PaperDeviceDomain(
                "d", "mode", tooManyValues));
        assertThrows(IllegalArgumentException.class, () -> new PaperEnvironmentDomain(
                "temperature", "environment", "temperature", List.of(), List.of("+1")));
        assertThrows(IllegalArgumentException.class, () -> new PaperEnvironmentDomain(
                "temperature", "environment", "temperature",
                List.of("20"), List.of("+1", "rate:1")));
        assertThrows(IllegalArgumentException.class, () -> new PaperEnvironmentDomain(
                "temperature", "environment", "temperature", List.of("20"), List.of("fast")));

        PaperEvent repeated = new PaperEvent(
                PaperEvent.Type.ENVIRONMENT, "temperature", "20", 1);
        assertThrows(IllegalArgumentException.class, () -> new PaperSeed(
                0L, Collections.nCopies(PaperSeed.MAX_EVENTS + 1, repeated)));
    }

    private static PaperEvent eventOfType(List<PaperEvent> events, PaperEvent.Type type) {
        return events.stream()
                .filter(event -> event.type() == type)
                .findFirst()
                .orElseThrow();
    }

    private static PaperEventDomainSnapshot domain() {
        return new PaperEventDomainSnapshot(
                5,
                List.of(new PaperDeviceDomain(
                        "thermostat", "mode", List.of("off", "heat"))),
                List.of(new PaperEnvironmentDomain(
                        "temperature",
                        "environment",
                        "temperature",
                        List.of("18", "21"),
                        List.of("-1", "+1"))));
    }
}
